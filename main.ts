import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const D = [[0, -1, 'u'], [0, 1, 'd'], [-1, 0, 'l'], [1, 0, 'r']];

function parse(text) {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const h = rows.length, w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1), goals = [], boxes = [];
  let player = -1;
  rows.forEach((row, y) => { for (let x = 0; x < row.length; x++) {
    const c = row[x], i = y * w + x;
    if (c === '#') continue;
    wall[i] = 0;
    if (c === '.' || c === '*' || c === '+') goals.push(i);
    if (c === '$' || c === '*') boxes.push(i);
    if (c === '@' || c === '+') player = i;
  }});
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++)
    if (!x || !y || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
  return { w, wall, goals, boxes: boxes.sort((a, b) => a - b), player };
}
function liveSq(w, wall, goals) {
  const live = new Uint8Array(wall.length), q = [...goals];
  for (const g of goals) live[g] = 1;
  for (let i = 0; i < q.length; i++) for (const [dx, dy] of D) {
    const d = dy * w + dx, y = q[i] - d;
    if (!wall[y] && !wall[y - d] && !live[y]) { live[y] = 1; q.push(y); }
  }
  return live;
}
function reach(w, wall, occ, from, seen, stamp, stack) {
  let low = from, n = 0;
  stack[n++] = from; seen[from] = stamp;
  while (n) {
    const p = stack[--n];
    if (p < low) low = p;
    for (const q of [p - w, p + w, p - 1, p + 1])
      if (!wall[q] && !occ[q] && seen[q] !== stamp) { seen[q] = stamp; stack[n++] = q; }
  }
  return low;
}
function frozen(w, wall, occ, goal, t) {
  for (const a of [t, t - 1, t - w, t - w - 1]) {
    const b = a + 1, c = a + w, d = c + 1;
    if (!(wall[a] || occ[a]) || !(wall[b] || occ[b]) || !(wall[c] || occ[c]) || !(wall[d] || occ[d])) continue;
    if ((occ[a] && !goal[a]) || (occ[b] && !goal[b]) || (occ[c] && !goal[c]) || (occ[d] && !goal[d])) return true;
  }
  return false;
}
function walkTo(w, wall, occ, from, to) {
  if (from === to) return '';
  const prev = new Int32Array(wall.length).fill(-1), how = new Array(wall.length), q = [from];
  prev[from] = from;
  for (let i = 0; i < q.length; i++) {
    const p = q[i];
    if (p === to) break;
    for (const [dx, dy, ch] of D) {
      const s = p + dy * w + dx;
      if (wall[s] || occ[s] || prev[s] !== -1) continue;
      prev[s] = p; how[s] = ch; q.push(s);
    }
  }
  let s = '';
  for (let p = to; p !== from; p = prev[p]) s = how[p] + s;
  return s;
}
function solveSub(w, wall, goals, boxes0, player0) {
  const size = wall.length, goal = new Uint8Array(size);
  for (const g of goals) goal[g] = 1;
  const live = liveSq(w, wall, goals);
  if (boxes0.some((b) => !live[b])) return null;
  const occ = new Uint8Array(size), seen = new Int32Array(size), mark = new Int32Array(size), stack = new Int32Array(size);
  let stamp = 0;
  const solved = (bs) => bs.every((b) => goal[b]);
  const keyOf = (bs, low) => low + '|' + bs.join(',');
  const sB = [boxes0], sP = [player0], parent = [-1], index = new Map();
  for (const b of boxes0) occ[b] = 1;
  index.set(keyOf(boxes0, reach(w, wall, occ, player0, seen, ++stamp, stack)), 0);
  for (const b of boxes0) occ[b] = 0;
  let found = solved(boxes0) ? 0 : -1;
  for (let head = 0; found < 0 && head < sB.length; head++) {
    const boxes = sB[head];
    for (const b of boxes) occ[b] = 1;
    reach(w, wall, occ, sP[head], seen, ++stamp, stack);
    const here = stamp;
    for (let bi = 0; bi < boxes.length && found < 0; bi++) {
      const b = boxes[bi];
      for (const [dx, dy] of D) {
        const d = dy * w + dx, t = b + d;
        if (seen[b - d] !== here || wall[t] || occ[t] || !live[t]) continue;
        occ[b] = 0; occ[t] = 1;
        const froz = frozen(w, wall, occ, goal, t);
        let key = null, next = null;
        if (!froz) {
          next = boxes.slice(); next[bi] = t; next.sort((a, z) => a - z);
          key = keyOf(next, reach(w, wall, occ, b, mark, ++stamp, stack));
        }
        occ[t] = 0; occ[b] = 1;
        if (froz || index.has(key)) continue;
        if (sB.length >= 250000) return null;
        index.set(key, sB.length);
        sB.push(next); sP.push(b); parent.push(head);
        if (solved(next)) { found = sB.length - 1; break; }
      }
    }
    for (const b of boxes) occ[b] = 0;
  }
  if (found < 0) return null;
  const path = [];
  for (let s = found; s > 0; s = parent[s]) path.push(s);
  path.reverse();
  let moves = '', player = player0, boxes = boxes0;
  
  for (const s of path) {
    const nb = sB[s];
    const from = boxes.find((b) => !nb.includes(b));
    const to = nb.find((b) => !boxes.includes(b));
    const d = to - from;
    const dir = D.find(([dx, dy]) => dy * w + dx === d);
    for (const b of boxes) occ[b] = 1;
    moves += walkTo(w, wall, occ, player, from - d);
    for (const b of boxes) occ[b] = 0;
    moves += dir[2];
    player = from; boxes = nb;
  }
  return { pushes: path.length, moves };
}
function solve(level) {
  const { w, wall, goals, boxes, player } = level;
  const live = liveSq(w, wall, goals);
  const row = Math.floor(player / w), cut = new Uint8Array(wall.length);
  for (let i = row * w; i < (row + 1) * w; i++) if (!wall[i] && !live[i]) cut[i] = 1;
  let rooms = null;
  if (!boxes.some((b) => cut[b])) {
    const part = new Int32Array(wall.length).fill(-1), list = [];
    for (let s = 0; s < wall.length; s++) {
      if (wall[s] || cut[s] || part[s] >= 0) continue;
      const squares = [s];
      part[s] = list.length;
      for (let i = 0; i < squares.length; i++) for (const [dx, dy] of D) {
        const q = squares[i] + dy * w + dx;
        if (!wall[q] && !cut[q] && part[q] < 0) { part[q] = list.length; squares.push(q); }
      }
      list.push({ boxes: [], goals: [], done: false });
    }
    for (const b of boxes) list[part[b]].boxes.push(b);
    for (const g of goals) if (part[g] >= 0) list[part[g]].goals.push(g);
    if (!goals.some((g) => part[g] < 0) && !list.some((r) => r.boxes.length !== r.goals.length))
      rooms = list.filter((r) => r.boxes.length > 0);
  }
  if (rooms === null) {
    const s = solveSub(w, wall, goals, boxes, player);
    return s === null ? '' : s.moves;
  }
  let moves = '', cur = player;
  for (const room of rooms) {
    const w2 = wall.slice();
    for (const other of rooms) if (other !== room)
      for (const b of other.done ? other.goals : other.boxes) w2[b] = 1;
    const s = solveSub(w, w2, room.goals.slice().sort((a, b) => a - b), room.boxes.slice().sort((a, b) => a - b), cur);
    if (s === null) return '';
    moves += s.moves;
    for (const ch of s.moves) cur += ch === 'u' ? -w : ch === 'd' ? w : ch === 'l' ? -1 : 1;
    room.done = true;
  }
  return moves;
}
for (const id of readdirSync(I).sort()) {
  const moves = solve(parse(readFileSync(join(I, id, 'level.txt'), 'utf8')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
