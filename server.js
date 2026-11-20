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

const queue = new Map(); // username -> lastSeen
const userMatch = new Map(); // username -> matchId (المباراة الجارية)
for (const m of Object.values(db.matches)) {
  if (m.status === 'playing') for (const p of m.players) userMatch.set(p, m.id);
}

// ---------- أدوات ----------
const now = () => Date.now();
function hashPw(pw, salt) { return crypto.scryptSync(pw, salt, 32).toString('hex'); }
function newToken() { return crypto.randomBytes(24).toString('hex'); }

function loadQuestions() {
  let arr = [];
  try { arr = JSON.parse(fs.readFileSync(QUESTIONS_FILE, 'utf8')); } catch (e) { return []; }
  return arr.filter(q => q && typeof q.q === 'string' && Array.isArray(q.options) &&
    q.options.length >= 2 && Number.isInteger(q.answer) && q.answer >= 0 && q.answer < q.options.length);
}
function shuffle(a) {
  a = a.slice();
  for (let i = a.length - 1; i > 0; i--) { const j = crypto.randomInt(i + 1); [a[i], a[j]] = [a[j], a[i]]; }
  return a;
}

// ---------- منطق المباراة ----------
function createMatch(a, b) {
  const pool = loadQuestions();
  const qs = shuffle(pool).slice(0, QUESTIONS_PER_MATCH).map(q => {
    // نخلط ترتيب الاختيارات أيضاً
    const idx = shuffle(q.options.map((_, i) => i));
    return { q: q.q, options: idx.map(i => q.options[i]), answer: idx.indexOf(q.answer) };
  });
  if (!qs.length) return null;
  const t = now() + START_DELAY_MS;
  const id = crypto.randomBytes(8).toString('hex');
  const m = {
    id, players: [a, b], qs, status: 'playing', createdAt: now(),
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

function tryMatchmake(me) {
  for (const [u, seen] of queue) if (now() - seen > QUEUE_STALE_MS) queue.delete(u);
  for (const u of queue.keys()) {
    if (u !== me) {
      queue.delete(u); queue.delete(me);
      return createMatch(u, me);
    }
  }
  queue.set(me, now());
  return null;
}

// ---------- عرض الحالة للّاعب ----------
function viewFor(m, me) {
  advance(m);
  const opp = m.players.find(p => p !== me);
  const mine = m.p[me], theirs = m.p[opp];
  const v = {
    id: m.id, status: m.status, opponent: opp, total: m.qs.length,
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
function readBody(req) {
  return new Promise((resolve) => {
    let d = '';
    req.on('data', c => { d += c; if (d.length > 10000) req.destroy(); });
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

async function api(req, res, url) {
  const me = getUser(req);
  const ip = req.socket.remoteAddress;

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
      queue.set(me, now());
      // قد يكون لاعب آخر دخل الطابور للتو
      const m = tryMatchmake(me);
      if (m) return send(res, 200, { profile, status: 'match', match: viewFor(m, me) });
      return send(res, 200, { profile, status: 'waiting' });
    }
    // آخر مباراة منتهية (لعرض النتيجة)
    const last = db.users[me].lastMatch && db.matches[db.users[me].lastMatch];
    return send(res, 200, { profile, status: 'idle', last: last && last.status === 'finished' ? viewFor(last, me) : null });
  }

  if (url === '/api/queue/join' && req.method === 'POST') {
    if (userMatch.has(me)) return send(res, 200, { ok: true });
    if (!loadQuestions().length) return send(res, 503, { error: 'لا توجد أسئلة في البنك بعد' });
    tryMatchmake(me);
    return send(res, 200, { ok: true });
  }
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
    if (url !== '/' && url !== '/index.html') { res.writeHead(404); return res.end('Not found'); }
    fs.readFile(path.join(__dirname, 'index.html'), (err, buf) => {
      if (err) { res.writeHead(500); return res.end('index.html missing'); }
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' });
      res.end(buf);
    });
  } catch (e) { console.error(e); send(res, 500, { error: 'خطأ في الخادم' }); }
});
if (require.main === module) server.listen(PORT, () => console.log('Quiz Battle running on http://localhost:' + PORT));
module.exports = server;
