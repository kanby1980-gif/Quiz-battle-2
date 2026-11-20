// منصة تحدّي المعلومات — خادم بدون أي مكتبات خارجية (Node 18+)
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const PORT = process.env.PORT || 3000;
const DATA_FILE = process.env.DATA_FILE || path.join(__dirname, 'data.json');
const QUESTIONS_FILE = path.join(__dirname, 'questions.json');

const QUESTIONS_PER_MATCH = 15;
const SECONDS_PER_QUESTION = 20;
const START_DELAY_MS = 3000; // عدّاد البداية
const QUEUE_STALE_MS = 8000;
const MIN_QUESTIONS_TO_PLAY = 5; // أقل عدد أسئلة لتفعيل المجموعة للّاعبين
const DEFAULT_CAT = 'عام';

// ---------- التخزين ----------
let db = { users: {}, sessions: {}, matches: {} };
try { db = Object.assign(db, JSON.parse(fs.readFileSync(DATA_FILE, 'utf8'))); } catch (e) {}
let saveTimer = null;
function save() {
  if (saveTimer) return;
  saveTimer = setTimeout(() => {
    saveTimer = null;
    const tmp = DATA_FILE + '.tmp';
    fs.writeFile(tmp, JSON.stringify(db), (err) => { if (!err) fs.rename(tmp, DATA_FILE, () => {}); });
  }, 300);
}

const queue = new Map(); // username -> { seen, cat }
const userMatch = new Map(); // username -> matchId (المباراة الجارية)
for (const m of Object.values(db.matches)) {
  if (m.status === 'playing') for (const p of m.players) userMatch.set(p, m.id);
}

// ---------- أدوات ----------
const now = () => Date.now();
function hashPw(pw, salt) { return crypto.scryptSync(pw, salt, 32).toString('hex'); }
function newToken() { return crypto.randomBytes(24).toString('hex'); }

const validQ = q => q && typeof q.q === 'string' && q.q.trim() && Array.isArray(q.options) &&
  q.options.length >= 2 && q.options.length <= 6 && q.options.every(o => typeof o === 'string' && o.trim()) &&
  Number.isInteger(q.answer) && q.answer >= 0 && q.answer < q.options.length;
const newId = () => crypto.randomBytes(5).toString('hex');
if (!Array.isArray(db.categories)) db.categories = [];
function catByName(name, create) {
  name = String(name || '').trim().slice(0, 30);
  let c = db.categories.find(c => c.name === name);
  if (!c && create && name) { c = { id: newId(), name }; db.categories.push(c); }
  return c;
}
// أول تشغيل: نملأ بنك الأسئلة من questions.json (يدعم حقل cat = اسم المجموعة)
if (!Array.isArray(db.questions)) {
  let arr = [];
  try { arr = JSON.parse(fs.readFileSync(QUESTIONS_FILE, 'utf8')); } catch (e) {}
  db.questions = arr.filter(validQ).map(q => ({
    id: newId(), cat: catByName(q.cat || DEFAULT_CAT, true).id,
    q: q.q.trim(), options: q.options.map(o => o.trim()), answer: q.answer }));
  save();
}
// ترقية الأسئلة القديمة التي لا تنتمي لمجموعة
if (db.questions.some(q => !q.cat || !db.categories.find(c => c.id === q.cat))) {
  const def = catByName(DEFAULT_CAT, true);
  db.questions.forEach(q => { if (!q.cat || !db.categories.find(c => c.id === q.cat)) q.cat = def.id; });
  save();
}
function loadQuestions(cat) { return db.questions.filter(q => q.cat === cat && validQ(q)); }
function catCounts() {
  return db.categories.map(c => ({ id: c.id, name: c.name, count: db.questions.filter(q => q.cat === c.id && validQ(q)).length }));
}

// نص جماعي: كل سؤال في فقرة، أول سطر السؤال، ثم الاختيارات، والصحيح يبدأ بـ *
function parseBulk(text) {
  const out = [], errors = [];
  const t = String(text || '').trim();
  if (t.startsWith('[')) {
    try {
      JSON.parse(t).forEach((q, i) => validQ(q) ? out.push({ q: q.q.trim(), options: q.options.map(o => o.trim()), answer: q.answer }) : errors.push('عنصر JSON رقم ' + (i + 1) + ' غير صالح'));
      return { out, errors };
    } catch (e) { return { out, errors: ['صيغة JSON غير صحيحة'] }; }
  }
  t.split(/\n\s*\n/).filter(b => b.trim()).forEach((block, i) => {
    const lines = block.split('\n').map(l => l.trim()).filter(Boolean);
    const q = lines[0], opts = lines.slice(1);
    const marked = opts.map((o, k) => /^[*✓]/.test(o) ? k : -1).filter(k => k >= 0);
    const options = opts.map(o => o.replace(/^[*✓]\s*/, '').trim());
    if (opts.length < 2 || opts.length > 6) errors.push('السؤال ' + (i + 1) + ': لازم من 2 إلى 6 اختيارات');
    else if (marked.length !== 1) errors.push('السؤال ' + (i + 1) + ': علّم الإجابة الصحيحة بنجمة * واحدة');
    else out.push({ q, options, answer: marked[0] });
  });
  return { out, errors };
}
function shuffle(a) {
  a = a.slice();
  for (let i = a.length - 1; i > 0; i--) { const j = crypto.randomInt(i + 1); [a[i], a[j]] = [a[j], a[i]]; }
  return a;
}

// ---------- منطق المباراة ----------
function createMatch(a, b, cat) {
  const pool = loadQuestions(cat);
  const qs = shuffle(pool).slice(0, QUESTIONS_PER_MATCH).map(q => {
    // نخلط ترتيب الاختيارات أيضاً
    const idx = shuffle(q.options.map((_, i) => i));
    return { q: q.q, options: idx.map(i => q.options[i]), answer: idx.indexOf(q.answer) };
  });
  if (!qs.length) return null;
  const t = now() + START_DELAY_MS;
  const id = crypto.randomBytes(8).toString('hex');
  const m = {
    id, cat, players: [a, b], qs, status: 'playing', createdAt: now(),
    p: {
      [a]: { answers: [], times: [], qStart: t },
      [b]: { answers: [], times: [], qStart: t },
    },
    result: null,
  };
  db.matches[id] = m;
  userMatch.set(a, id); userMatch.set(b, id);
  save();
  return m;
}

// يُنهي الأسئلة التي انتهى وقتها تلقائياً
function advance(m) {
  if (m.status !== 'playing') return;
  const limit = SECONDS_PER_QUESTION * 1000;
  for (const u of m.players) {
    const s = m.p[u];
    while (s.answers.length < m.qs.length && now() > s.qStart + limit) {
      s.answers.push(null); s.times.push(limit); s.qStart += limit;
    }
  }
  if (m.players.every(u => m.p[u].answers.length >= m.qs.length)) finish(m);
}

function scoreOf(m, u) {
  const s = m.p[u];
  let score = 0, time = 0;
  s.answers.forEach((a, i) => { if (a === m.qs[i].answer) score++; time += s.times[i]; });
  return { score, time };
}

function finish(m) {
  const [a, b] = m.players;
  const A = scoreOf(m, a), B = scoreOf(m, b);
  let winner = null;
  if (A.score !== B.score) winner = A.score > B.score ? a : b;
  else if (Math.abs(A.time - B.time) > 50) winner = A.time < B.time ? a : b;
  m.status = 'finished';
  m.result = { winner, scores: { [a]: A, [b]: B } };
  for (const u of m.players) {
    const usr = db.users[u]; if (!usr) continue;
    if (winner === null) usr.draws++; else if (winner === u) usr.wins++; else usr.losses++;
    usr.lastMatch = m.id; // لعرض النتيجة حتى لو أُعيد تحميل الصفحة
    userMatch.delete(u);
  }
  save();
}

function tryMatchmake(me, cat) {
  for (const [u, e] of queue) if (now() - e.seen > QUEUE_STALE_MS) queue.delete(u);
  for (const [u, e] of queue) {
    if (u !== me && e.cat === cat) {
      queue.delete(u); queue.delete(me);
      return createMatch(u, me, cat);
    }
  }
  queue.set(me, { seen: now(), cat });
  return null;
}

// ---------- عرض الحالة للّاعب ----------
function viewFor(m, me) {
  advance(m);
  const opp = m.players.find(p => p !== me);
  const mine = m.p[me], theirs = m.p[opp];
  const v = {
    id: m.id, status: m.status, opponent: opp, total: m.qs.length,
    cat: m.cat, catName: (db.categories.find(c => c.id === m.cat) || {}).name || '',
    secondsPerQuestion: SECONDS_PER_QUESTION,
    myAnswered: mine.answers.length, oppAnswered: theirs.answers.length,
  };
  if (m.status === 'playing') {
    if (mine.answers.length < m.qs.length) {
      const q = m.qs[mine.answers.length];
      v.current = { index: mine.answers.length, q: q.q, options: q.options };
      v.startsInMs = Math.max(0, mine.qStart - now());
      v.remainingMs = Math.max(0, mine.qStart + SECONDS_PER_QUESTION * 1000 - now());
    } else v.waitingForOpponent = true;
  } else {
    const r = m.result;
    v.outcome = r.winner === null ? 'draw' : (r.winner === me ? 'win' : 'lose');
    v.myScore = r.scores[me].score; v.oppScore = r.scores[opp].score;
    v.review = m.qs.map((q, i) => ({
      q: q.q, options: q.options, correct: q.answer, mine: mine.answers[i], theirs: theirs.answers[i],
    }));
  }
  return v;
}

// ---------- HTTP ----------
function send(res, code, obj, headers = {}) {
  const body = JSON.stringify(obj);
  res.writeHead(code, Object.assign({ 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' }, headers));
  res.end(body);
}
function readBody(req, max = 10000) {
  return new Promise((resolve) => {
    let d = '';
    req.on('data', c => { d += c; if (d.length > max) req.destroy(); });
    req.on('end', () => { try { resolve(JSON.parse(d || '{}')); } catch (e) { resolve({}); } });
  });
}
function getUser(req) {
  const c = (req.headers.cookie || '').split(';').map(s => s.trim()).find(s => s.startsWith('sid='));
  if (!c) return null;
  const u = db.sessions[c.slice(4)];
  return u && db.users[u] ? u : null;
}
function cookie(token, maxAge) {
  return { 'Set-Cookie': `sid=${token}; HttpOnly; SameSite=Lax; Path=/; Max-Age=${maxAge}` };
}
const USERNAME_RE = /^[A-Za-z0-9_؀-ۿ]{3,20}$/;

// حدّ بسيط لمحاولات الدخول لكل IP
const attempts = new Map();
function tooMany(ip) {
  const a = (attempts.get(ip) || []).filter(t => now() - t < 60000);
  a.push(now()); attempts.set(ip, a);
  return a.length > 20;
}

const catByName2 = id => db.categories.find(c => c.id === id);
function isAdmin(req) {
  const pw = process.env.ADMIN_PASSWORD;
  const given = String(req.headers['x-admin-password'] || '');
  if (!pw) return false;
  const a = crypto.createHash('sha256').update(given).digest(), b = crypto.createHash('sha256').update(pw).digest();
  return crypto.timingSafeEqual(a, b);
}

async function adminApi(req, res, url, ip) {
  if (!process.env.ADMIN_PASSWORD) return send(res, 503, { error: 'لم يتم ضبط ADMIN_PASSWORD على الخادم' });
  if (tooMany(ip)) return send(res, 429, { error: 'محاولات كثيرة، انتظر قليلاً' });
  if (!isAdmin(req)) return send(res, 401, { error: 'كلمة مرور الأدمن غير صحيحة' });
  if (url === '/api/admin/questions' && req.method === 'GET')
    return send(res, 200, { questions: db.questions, categories: catCounts(), users: Object.keys(db.users).length, matches: Object.keys(db.matches).length, perMatch: QUESTIONS_PER_MATCH, min: MIN_QUESTIONS_TO_PLAY });
  if (url === '/api/admin/cat/add' && req.method === 'POST') {
    const b = await readBody(req); const name = String(b.name || '').trim().slice(0, 30);
    if (!name) return send(res, 400, { error: 'اكتب اسم المجموعة' });
    if (catByName(name)) return send(res, 409, { error: 'المجموعة موجودة بالفعل' });
    const c = catByName(name, true); save();
    return send(res, 200, { ok: true, id: c.id });
  }
  if (url === '/api/admin/cat/rename' && req.method === 'POST') {
    const b = await readBody(req); const c = catByName2(b.id); const name = String(b.name || '').trim().slice(0, 30);
    if (!c || !name) return send(res, 400, { error: 'بيانات غير صالحة' });
    if (db.categories.some(x => x.name === name && x.id !== c.id)) return send(res, 409, { error: 'الاسم مستخدم' });
    c.name = name; save(); return send(res, 200, { ok: true });
  }
  if (url === '/api/admin/cat/delete' && req.method === 'POST') {
    const b = await readBody(req);
    db.categories = db.categories.filter(c => c.id !== b.id);
    db.questions = db.questions.filter(q => q.cat !== b.id); save();
    return send(res, 200, { ok: true });
  }
  if (url === '/api/admin/add' && req.method === 'POST') {
    const b = await readBody(req);
    if (!catByName2(b.cat)) return send(res, 400, { error: 'اختر المجموعة أولاً' });
    const q = { q: String(b.q || '').trim(), options: Array.isArray(b.options) ? b.options.map(o => String(o).trim()).filter(Boolean) : [], answer: b.answer };
    if (!validQ(q)) return send(res, 400, { error: 'السؤال غير مكتمل: اكتب السؤال و2-6 اختيارات وحدد الصحيح' });
    db.questions.push(Object.assign({ id: newId(), cat: b.cat }, q)); save();
    return send(res, 200, { ok: true });
  }
  if (url === '/api/admin/bulk' && req.method === 'POST') {
    const b = await readBody(req, 500000);
    if (!catByName2(b.cat)) return send(res, 400, { error: 'اختر المجموعة أولاً', added: 0, errors: [] });
    const { out, errors } = parseBulk(b.text);
    out.forEach(q => db.questions.push(Object.assign({ id: newId(), cat: b.cat }, q))); if (out.length) save();
    return send(res, 200, { added: out.length, errors });
  }
  if (url === '/api/admin/delete' && req.method === 'POST') {
    const b = await readBody(req);
    db.questions = db.questions.filter(q => q.id !== b.id); save();
    return send(res, 200, { ok: true });
  }
  return send(res, 404, { error: 'غير موجود' });
}

async function api(req, res, url) {
  const me = getUser(req);
  const ip = req.socket.remoteAddress;
  if (url.startsWith('/api/admin/')) return adminApi(req, res, url, ip);

  if (url === '/api/register' && req.method === 'POST') {
    if (tooMany(ip)) return send(res, 429, { error: 'محاولات كثيرة، انتظر قليلاً' });
    const { username, password } = await readBody(req);
    if (typeof username !== 'string' || !USERNAME_RE.test(username)) return send(res, 400, { error: 'اسم المستخدم من 3 إلى 20 حرفاً (حروف أو أرقام أو _)' });
    if (typeof password !== 'string' || password.length < 6) return send(res, 400, { error: 'كلمة المرور 6 أحرف على الأقل' });
    const key = username.toLowerCase();
    if (Object.keys(db.users).some(u => u.toLowerCase() === key)) return send(res, 409, { error: 'اسم المستخدم مستخدم بالفعل' });
    const salt = crypto.randomBytes(16).toString('hex');
    db.users[username] = { salt, hash: hashPw(password, salt), wins: 0, losses: 0, draws: 0, created: now() };
    const token = newToken(); db.sessions[token] = username; save();
    return send(res, 200, { ok: true }, cookie(token, 60 * 60 * 24 * 30));
  }
  if (url === '/api/login' && req.method === 'POST') {
    if (tooMany(ip)) return send(res, 429, { error: 'محاولات كثيرة، انتظر قليلاً' });
    const { username, password } = await readBody(req);
    const u = typeof username === 'string' && db.users[username];
    if (!u || typeof password !== 'string' ||
        !crypto.timingSafeEqual(Buffer.from(hashPw(password, u.salt), 'hex'), Buffer.from(u.hash, 'hex')))
      return send(res, 401, { error: 'اسم المستخدم أو كلمة المرور غير صحيحة' });
    const token = newToken(); db.sessions[token] = username; save();
    return send(res, 200, { ok: true }, cookie(token, 60 * 60 * 24 * 30));
  }
  if (url === '/api/logout' && req.method === 'POST') {
    const c = (req.headers.cookie || '').split(';').map(s => s.trim()).find(s => s.startsWith('sid='));
    if (c) { delete db.sessions[c.slice(4)]; save(); }
    if (me) queue.delete(me);
    return send(res, 200, { ok: true }, cookie('', 0));
  }

  if (!me) return send(res, 401, { error: 'غير مسجّل' });

  if (url === '/api/state' && req.method === 'GET') {
    const u = db.users[me];
    const profile = { username: me, wins: u.wins, losses: u.losses, draws: u.draws };
    const mid = userMatch.get(me);
    if (mid) return send(res, 200, { profile, status: 'match', match: viewFor(db.matches[mid], me) });
    if (queue.has(me)) {
      const cat = queue.get(me).cat;
      // قد يكون لاعب آخر دخل الطابور للتو
      const m = tryMatchmake(me, cat);
      if (m) return send(res, 200, { profile, status: 'match', match: viewFor(m, me) });
      return send(res, 200, { profile, status: 'waiting', catName: (catByName2(cat) || {}).name || '' });
    }
    // آخر مباراة منتهية (لعرض النتيجة)
    const last = db.users[me].lastMatch && db.matches[db.users[me].lastMatch];
    return send(res, 200, { profile, status: 'idle', last: last && last.status === 'finished' ? viewFor(last, me) : null });
  }

  if (url === '/api/queue/join' && req.method === 'POST') {
    if (userMatch.has(me)) return send(res, 200, { ok: true });
    const b = await readBody(req);
    const c = catByName2(b.cat);
    if (!c) return send(res, 400, { error: 'اختر مجموعة' });
    if (loadQuestions(c.id).length < MIN_QUESTIONS_TO_PLAY) return send(res, 503, { error: 'هذه المجموعة لا تحتوي أسئلة كافية بعد' });
    queue.delete(me);
    tryMatchmake(me, c.id);
    return send(res, 200, { ok: true });
  }
  if (url === '/api/categories' && req.method === 'GET')
    return send(res, 200, { categories: catCounts().map(c => Object.assign(c, { playable: c.count >= MIN_QUESTIONS_TO_PLAY })), perMatch: QUESTIONS_PER_MATCH });
  if (url === '/api/queue/leave' && req.method === 'POST') {
    queue.delete(me); return send(res, 200, { ok: true });
  }
  if (url === '/api/answer' && req.method === 'POST') {
    const { qIndex, choice } = await readBody(req);
    const mid = userMatch.get(me);
    if (!mid) return send(res, 409, { error: 'لا توجد مباراة' });
    const m = db.matches[mid];
    advance(m);
    if (m.status !== 'playing') return send(res, 200, { ok: true });
    const s = m.p[me];
    if (qIndex !== s.answers.length || s.answers.length >= m.qs.length) return send(res, 200, { ok: true }); // قديم/مكرر
    if (now() < s.qStart) return send(res, 400, { error: 'لم تبدأ المباراة بعد' });
    const ch = Number.isInteger(choice) && choice >= 0 && choice < m.qs[qIndex].options.length ? choice : null;
    const t = Math.min(now() - s.qStart, SECONDS_PER_QUESTION * 1000);
    s.answers.push(ch); s.times.push(t); s.qStart = now();
    if (m.players.every(u => m.p[u].answers.length >= m.qs.length)) finish(m);
    save();
    return send(res, 200, { ok: true });
  }
  if (url === '/api/dismiss' && req.method === 'POST') {
    delete db.users[me].lastMatch; save(); return send(res, 200, { ok: true });
  }
  if (url === '/api/leaderboard' && req.method === 'GET') {
    const rows = Object.entries(db.users)
      .map(([name, u]) => ({ name, wins: u.wins, losses: u.losses, draws: u.draws }))
      .sort((a, b) => b.wins - a.wins || a.losses - b.losses).slice(0, 20);
    return send(res, 200, { rows });
  }
  return send(res, 404, { error: 'غير موجود' });
}

const server = http.createServer(async (req, res) => {
  try {
    const url = req.url.split('?')[0];
    if (url.startsWith('/api/')) return await api(req, res, url);
    const page = url === '/admin' || url === '/admin.html' ? 'admin.html' : (url === '/' || url === '/index.html' ? 'index.html' : null);
    if (!page) { res.writeHead(404); return res.end('Not found'); }
    fs.readFile(path.join(__dirname, page), (err, buf) => {
      if (err) { res.writeHead(500); return res.end('page missing'); }
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' });
      res.end(buf);
    });
  } catch (e) { console.error(e); send(res, 500, { error: 'خطأ في الخادم' }); }
});
if (require.main === module) server.listen(PORT, () => console.log('Quiz Battle running on http://localhost:' + PORT));
module.exports = server;
