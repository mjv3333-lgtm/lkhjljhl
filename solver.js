/**
 * Connect 5 Solver Engine
 * Browser-based AI for a 9x7 Connect Five game with gravity (Connect Four style).
 *
 * Board layout: COLS=9, ROWS=7, gravity applies (pieces fall to bottom).
 * Win condition: 5 or more in a row horizontally, vertically, or diagonally.
 */

(function (global) {
  'use strict';

  // ─── Constants ────────────────────────────────────────────────────────────
  const COLS = 9;
  const ROWS = 7;
  const SIZE = COLS * ROWS; // 63
  const EMPTY = 0;
  const P1 = 1;
  const P2 = 2;

  const WIN_LENGTH = 5;
  const MAX_DEPTH = 32;

  // Transposition table flags
  const EXACT = 0;
  const LOWER = 1; // lower bound (fail-high / beta cut)
  const UPPER = 2; // upper bound (fail-low / all-node)

  const INF = 10000000;
  const WIN_SCORE = 5000000;
  const DRAW_SCORE = 0;

  // ─── Column order for move ordering (center-first) ────────────────────────
  // Pre-sorted center-preferred column order: 4,3,5,2,6,1,7,0,8
  const COL_ORDER = new Int32Array([4, 3, 5, 2, 6, 1, 7, 0, 8]);

  // ─── Zobrist Hashing (64-bit emulated with two 32-bit halves) ─────────────
  // Tables: zobristHi/Lo indexed by (player-1)*COLS*ROWS + col*ROWS + row
  const zobristHi = new Uint32Array(2 * COLS * ROWS);
  const zobristLo = new Uint32Array(2 * COLS * ROWS);

  function zobristIndex(player, col, row) {
    return (player - 1) * COLS * ROWS + col * ROWS + row;
  }

  (function initZobrist() {
    // XOR-shift PRNG for deterministic initialization
    let seed = 0xdeadbeef >>> 0;
    function rand32() {
      seed ^= seed << 13;
      seed ^= seed >>> 17;
      seed ^= seed << 5;
      return seed >>> 0;
    }
    for (let i = 0; i < zobristHi.length; i++) {
      zobristHi[i] = rand32();
      zobristLo[i] = rand32();
    }
  })();

  // ─── Positional Bonus Table ────────────────────────────────────────────────
  // Precomputed bonus for each cell based on proximity to center.
  const posBonus = new Int32Array(SIZE);
  (function initPosBonus() {
    const centerCol = (COLS - 1) / 2; // 4
    const centerRow = (ROWS - 1) / 2; // 3
    for (let c = 0; c < COLS; c++) {
      for (let r = 0; r < ROWS; r++) {
        const dc = Math.abs(c - centerCol);
        const dr = Math.abs(r - centerRow);
        posBonus[c * ROWS + r] = Math.max(0, 4 - dc) + Math.max(0, 3 - dr);
      }
    }
  })();

  // ─── Board Creation ────────────────────────────────────────────────────────
  /**
   * Create a fresh board state.
   * @returns {{ cells: Uint8Array, heights: Int32Array, moveCount: number,
   *             history: Int32Array, historyTop: number, hashHi: number, hashLo: number }}
   */
  function createBoard() {
    return {
      cells: new Uint8Array(SIZE),
      heights: new Int32Array(COLS),   // next available row index per column (0 = empty)
      moveCount: 0,
      history: new Int32Array(SIZE),   // stack of columns played (for undo)
      historyTop: 0,
      hashHi: 0,
      hashLo: 0,
    };
  }

  /** Clone a board (not used in hot path). */
  function cloneBoard(board) {
    return {
      cells: new Uint8Array(board.cells),
      heights: new Int32Array(board.heights),
      moveCount: board.moveCount,
      history: new Int32Array(board.history),
      historyTop: board.historyTop,
      hashHi: board.hashHi,
      hashLo: board.hashLo,
    };
  }

  /** Flat index: col * ROWS + row */
  function idx(col, row) {
    return col * ROWS + row;
  }

  /**
   * Make a move. The current player is derived from moveCount (even = P1, odd = P2).
   * Returns false if column is full or out of range.
   */
  function makeMove(board, col) {
    if (col < 0 || col >= COLS) return false;
    const row = board.heights[col];
    if (row >= ROWS) return false;

    const player = (board.moveCount & 1) === 0 ? P1 : P2;
    const i = idx(col, row);

    board.cells[i] = player;
    board.heights[col] = row + 1;
    board.history[board.historyTop++] = col;
    board.moveCount++;

    // Update Zobrist hash
    const zi = zobristIndex(player, col, row);
    board.hashHi ^= zobristHi[zi];
    board.hashLo ^= zobristLo[zi];

    return true;
  }

  /** Undo the last move. */
  function undoMove(board) {
    if (board.historyTop === 0) return;
    const col = board.history[--board.historyTop];
    board.moveCount--;
    const player = (board.moveCount & 1) === 0 ? P1 : P2;
    const row = board.heights[col] - 1;
    const i = idx(col, row);

    // Undo Zobrist hash
    const zi = zobristIndex(player, col, row);
    board.hashHi ^= zobristHi[zi];
    board.hashLo ^= zobristLo[zi];

    board.cells[i] = EMPTY;
    board.heights[col] = row;
  }

  function isValidMove(board, col) {
    return col >= 0 && col < COLS && board.heights[col] < ROWS;
  }

  // ─── Win Detection ─────────────────────────────────────────────────────────
  /**
   * Fast win check around (col, row) for the given player.
   * Checks 4 directions: horizontal, vertical, diag ↗, diag ↘.
   * Examines at most 4 cells in each direction → O(1), bounded to 8 cells/dir.
   */
  const DIRS_DC = new Int32Array([1, 0, 1, 1]);
  const DIRS_DR = new Int32Array([0, 1, 1, -1]);

  function checkWin(cells, col, row, player) {
    for (let d = 0; d < 4; d++) {
      const dc = DIRS_DC[d];
      const dr = DIRS_DR[d];
      let count = 1;

      // positive direction
      let c = col + dc, r = row + dr;
      while (c >= 0 && c < COLS && r >= 0 && r < ROWS && cells[idx(c, r)] === player) {
        count++;
        c += dc;
        r += dr;
      }
      // negative direction
      c = col - dc; r = row - dr;
      while (c >= 0 && c < COLS && r >= 0 && r < ROWS && cells[idx(c, r)] === player) {
        count++;
        c -= dc;
        r -= dr;
      }

      if (count >= WIN_LENGTH) return true;
    }
    return false;
  }

  /**
   * Determine the winner by examining the last-placed piece.
   * Returns P1, P2, or 0 (no winner).
   */
  function getWinner(board) {
    if (board.historyTop === 0) return 0;
    const col = board.history[board.historyTop - 1];
    const row = board.heights[col] - 1;
    // The last player to move is moveCount-1 (since moveCount was already incremented)
    const player = ((board.moveCount - 1) & 1) === 0 ? P1 : P2;
    if (checkWin(board.cells, col, row, player)) return player;
    return 0;
  }

  function isDraw(board) {
    return board.moveCount >= SIZE;
  }

  // ─── Evaluation ────────────────────────────────────────────────────────────
  /**
   * Score a window of 5 cells. Returns score from `player`'s perspective.
   * positions: array of 5 cell indices.
   */
  function scoreWindow5(cells, p0, p1, p2, p3, p4, player, opponent) {
    let pCount = 0, oCount = 0;
    const v0 = cells[p0], v1 = cells[p1], v2 = cells[p2], v3 = cells[p3], v4 = cells[p4];
    if (v0 === player) pCount++; else if (v0 === opponent) oCount++;
    if (v1 === player) pCount++; else if (v1 === opponent) oCount++;
    if (v2 === player) pCount++; else if (v2 === opponent) oCount++;
    if (v3 === player) pCount++; else if (v3 === opponent) oCount++;
    if (v4 === player) pCount++; else if (v4 === opponent) oCount++;

    if (oCount > 0 && pCount > 0) return 0; // blocked window
    if (oCount > 0) return 0;                // opponent window (caller handles separately)

    const eCount = 5 - pCount;
    if (pCount === 5) return WIN_SCORE;
    if (pCount === 4 && eCount === 1) return 10000;
    if (pCount === 3 && eCount === 2) return 500;
    if (pCount === 2 && eCount === 3) return 50;
    return 0;
  }

  /**
   * Evaluate the board from `player`'s perspective.
   */
  function evaluate(board, player) {
    const cells = board.cells;
    const opponent = player === P1 ? P2 : P1;
    let score = 0;

    // Positional bonus for each placed piece
    for (let c = 0; c < COLS; c++) {
      const h = board.heights[c];
      for (let r = 0; r < h; r++) {
        const v = cells[idx(c, r)];
        const pb = posBonus[c * ROWS + r];
        if (v === player) score += pb;
        else if (v === opponent) score -= pb;
      }
    }

    let pOpenFours = 0;
    let oOpenFours = 0;

    // Horizontal windows
    for (let r = 0; r < ROWS; r++) {
      for (let c = 0; c <= COLS - WIN_LENGTH; c++) {
        const i0 = idx(c,r), i1=idx(c+1,r), i2=idx(c+2,r), i3=idx(c+3,r), i4=idx(c+4,r);
        const ps = scoreWindow5(cells, i0,i1,i2,i3,i4, player, opponent);
        const os = scoreWindow5(cells, i0,i1,i2,i3,i4, opponent, player);
        score += ps - os;
        if (ps === 10000) pOpenFours++;
        if (os === 10000) oOpenFours++;
      }
    }

    // Vertical windows
    for (let c = 0; c < COLS; c++) {
      for (let r = 0; r <= ROWS - WIN_LENGTH; r++) {
        const i0=idx(c,r), i1=idx(c,r+1), i2=idx(c,r+2), i3=idx(c,r+3), i4=idx(c,r+4);
        const ps = scoreWindow5(cells, i0,i1,i2,i3,i4, player, opponent);
        const os = scoreWindow5(cells, i0,i1,i2,i3,i4, opponent, player);
        score += ps - os;
        if (ps === 10000) pOpenFours++;
        if (os === 10000) oOpenFours++;
      }
    }

    // Diagonal ↗ windows (col+, row+)
    for (let c = 0; c <= COLS - WIN_LENGTH; c++) {
      for (let r = 0; r <= ROWS - WIN_LENGTH; r++) {
        const i0=idx(c,r), i1=idx(c+1,r+1), i2=idx(c+2,r+2), i3=idx(c+3,r+3), i4=idx(c+4,r+4);
        const ps = scoreWindow5(cells, i0,i1,i2,i3,i4, player, opponent);
        const os = scoreWindow5(cells, i0,i1,i2,i3,i4, opponent, player);
        score += ps - os;
        if (ps === 10000) pOpenFours++;
        if (os === 10000) oOpenFours++;
      }
    }

    // Diagonal ↘ windows (col+, row-)
    for (let c = 0; c <= COLS - WIN_LENGTH; c++) {
      for (let r = WIN_LENGTH - 1; r < ROWS; r++) {
        const i0=idx(c,r), i1=idx(c+1,r-1), i2=idx(c+2,r-2), i3=idx(c+3,r-3), i4=idx(c+4,r-4);
        const ps = scoreWindow5(cells, i0,i1,i2,i3,i4, player, opponent);
        const os = scoreWindow5(cells, i0,i1,i2,i3,i4, opponent, player);
        score += ps - os;
        if (ps === 10000) pOpenFours++;
        if (os === 10000) oOpenFours++;
      }
    }

    // Double-threat bonus: two or more open fours is nearly decisive
    if (pOpenFours >= 2) score += 50000;
    if (oOpenFours >= 2) score -= 50000;

    return score;
  }

  // ─── Threat Detection ──────────────────────────────────────────────────────
  /**
   * Count open-ended threats (windows with N pieces + empties, no opponent pieces)
   * for both players. Returns { p1: {twos,threes,fours}, p2: {twos,threes,fours} }
   */
  function countThreats(board) {
    const cells = board.cells;
    const result = {
      p1: { twos: 0, threes: 0, fours: 0 },
      p2: { twos: 0, threes: 0, fours: 0 },
    };

    function scan(i0,i1,i2,i3,i4) {
      let c1=0, c2=0, e=0;
      const vals = [cells[i0],cells[i1],cells[i2],cells[i3],cells[i4]];
      for (const v of vals) {
        if (v === P1) c1++;
        else if (v === P2) c2++;
        else e++;
      }
      if (c1 > 0 && c2 > 0) return; // mixed window
      if (c1 > 0) {
        if (c1 === 4 && e === 1) result.p1.fours++;
        else if (c1 === 3 && e === 2) result.p1.threes++;
        else if (c1 === 2 && e === 3) result.p1.twos++;
      } else if (c2 > 0) {
        if (c2 === 4 && e === 1) result.p2.fours++;
        else if (c2 === 3 && e === 2) result.p2.threes++;
        else if (c2 === 2 && e === 3) result.p2.twos++;
      }
    }

    for (let r = 0; r < ROWS; r++) {
      for (let c = 0; c <= COLS - WIN_LENGTH; c++) {
        scan(idx(c,r),idx(c+1,r),idx(c+2,r),idx(c+3,r),idx(c+4,r));
      }
    }
    for (let c = 0; c < COLS; c++) {
      for (let r = 0; r <= ROWS - WIN_LENGTH; r++) {
        scan(idx(c,r),idx(c,r+1),idx(c,r+2),idx(c,r+3),idx(c,r+4));
      }
    }
    for (let c = 0; c <= COLS - WIN_LENGTH; c++) {
      for (let r = 0; r <= ROWS - WIN_LENGTH; r++) {
        scan(idx(c,r),idx(c+1,r+1),idx(c+2,r+2),idx(c+3,r+3),idx(c+4,r+4));
      }
    }
    for (let c = 0; c <= COLS - WIN_LENGTH; c++) {
      for (let r = WIN_LENGTH - 1; r < ROWS; r++) {
        scan(idx(c,r),idx(c+1,r-1),idx(c+2,r-2),idx(c+3,r-3),idx(c+4,r-4));
      }
    }
    return result;
  }

  // ─── Transposition Table ───────────────────────────────────────────────────
  // Fixed-size typed-array TT with always-replace strategy.
  const TT_SIZE = 1 << 20; // ~1M entries (power of two for fast modulo)
  const TT_MASK = TT_SIZE - 1;
  const ttDepth_    = new Int32Array(TT_SIZE);
  const ttScore_    = new Int32Array(TT_SIZE);
  const ttFlag_     = new Uint8Array(TT_SIZE);
  const ttBestMove_ = new Int32Array(TT_SIZE).fill(-1);
  const ttHashHi_   = new Uint32Array(TT_SIZE);
  const ttHashLo_   = new Uint32Array(TT_SIZE);
  const ttValid_    = new Uint8Array(TT_SIZE);

  function ttClear() {
    ttValid_.fill(0);
  }

  function ttIndex(hashHi, hashLo) {
    // Mix hi and lo for good distribution
    return ((hashHi ^ Math.imul(hashLo, 0x9e3779b9 | 0)) >>> 0) & TT_MASK;
  }

  function ttStore(hashHi, hashLo, depth, score, flag, bestMove) {
    const i = ttIndex(hashHi, hashLo);
    // Always-replace: overwrite regardless
    ttHashHi_[i]   = hashHi;
    ttHashLo_[i]   = hashLo;
    ttDepth_[i]    = depth;
    ttScore_[i]    = score;
    ttFlag_[i]     = flag;
    ttBestMove_[i] = bestMove;
    ttValid_[i]    = 1;
  }

  // Shared result object filled by ttProbe (avoids allocation)
  const _ttResult = { depth: 0, score: 0, flag: 0, bestMove: -1 };

  function ttProbe(hashHi, hashLo) {
    const i = ttIndex(hashHi, hashLo);
    if (!ttValid_[i]) return false;
    if (ttHashHi_[i] !== hashHi || ttHashLo_[i] !== hashLo) return false;
    _ttResult.depth    = ttDepth_[i];
    _ttResult.score    = ttScore_[i];
    _ttResult.flag     = ttFlag_[i];
    _ttResult.bestMove = ttBestMove_[i];
    return true;
  }

  // ─── Killer Heuristic ──────────────────────────────────────────────────────
  // 2 killer slots per ply
  const killers = new Int32Array(MAX_DEPTH * 2).fill(-1);

  function killerStore(ply, move) {
    const base = ply * 2;
    if (killers[base] !== move) {
      killers[base + 1] = killers[base];
      killers[base] = move;
    }
  }

  function isKiller(ply, move) {
    const base = ply * 2;
    return killers[base] === move || killers[base + 1] === move;
  }

  // ─── History Heuristic ─────────────────────────────────────────────────────
  // history[player-1][col]: indexed as (player-1)*COLS + col
  const history = new Int32Array(2 * COLS);

  function historyReset() {
    history.fill(0);
  }

  function historyUpdate(player, col, depth) {
    history[(player - 1) * COLS + col] += depth * depth;
  }

  function historyScore(player, col) {
    return history[(player - 1) * COLS + col];
  }

  // ─── Move Generation ───────────────────────────────────────────────────────
  // Pre-allocated move and score buffers per ply (avoid hot-path allocations)
  const _moveLists  = [];
  const _moveScores = [];
  for (let i = 0; i < MAX_DEPTH + 4; i++) {
    _moveLists.push(new Int32Array(COLS));
    _moveScores.push(new Int32Array(COLS));
  }

  /**
   * Check whether placing in `col` results in an immediate win for `player`.
   * Temporarily modifies cells but restores them. Does NOT modify heights or hash.
   */
  function isImmediateWin(board, col, player) {
    const row = board.heights[col];
    if (row >= ROWS) return false;
    const i = idx(col, row);
    board.cells[i] = player;
    const win = checkWin(board.cells, col, row, player);
    board.cells[i] = EMPTY;
    return win;
  }

  /**
   * Generate moves ordered by heuristic score (descending).
   * Fills moveBuf[0..count-1] and scoreBuf[0..count-1].
   * Returns the number of valid moves.
   */
  function generateMoves(board, player, ply, moveBuf, scoreBuf) {
    const opponent = player === P1 ? P2 : P1;
    let count = 0;

    for (let oi = 0; oi < COLS; oi++) {
      const col = COL_ORDER[oi];
      if (!isValidMove(board, col)) continue;

      let score;

      // Priority 1: immediate win for us
      if (isImmediateWin(board, col, player)) {
        score = 100000000;
      }
      // Priority 2: block opponent immediate win
      else if (isImmediateWin(board, col, opponent)) {
        score = 90000000;
      }
      // Priority 3: killer move
      else if (isKiller(ply, col)) {
        score = 80000000;
      }
      // Priority 4: history + center preference
      else {
        score = historyScore(player, col) + (4 - Math.abs(col - 4)) * 1000;
      }

      moveBuf[count]  = col;
      scoreBuf[count] = score;
      count++;
    }

    // Insertion sort (N ≤ 9, so fast enough)
    for (let i = 1; i < count; i++) {
      const mv = moveBuf[i], sc = scoreBuf[i];
      let j = i - 1;
      while (j >= 0 && scoreBuf[j] < sc) {
        moveBuf[j + 1]  = moveBuf[j];
        scoreBuf[j + 1] = scoreBuf[j];
        j--;
      }
      moveBuf[j + 1]  = mv;
      scoreBuf[j + 1] = sc;
    }

    return count;
  }

  // ─── Principal Variation Storage ───────────────────────────────────────────
  // pvLength[ply]: how many moves are in the PV from ply 0 up to this point.
  //   Convention: pvLength[ply] = ply means 0 new moves contributed from this ply
  //               pvLength[ply] = ply+N means N moves stored at indices ply..ply+N-1
  // pvLine[ply][k]: the move at absolute ply k in the PV found at search ply `ply`.
  const pvLength = new Int32Array(MAX_DEPTH + 4);
  const pvLine   = [];
  for (let i = 0; i < MAX_DEPTH + 4; i++) {
    pvLine.push(new Int32Array(MAX_DEPTH + 4));
  }

  // ─── Search State ──────────────────────────────────────────────────────────
  let _nodes       = 0;
  let _startTime   = 0;
  let _timeLimitMs = 5000;
  let _timeUp      = false;

  function checkTime() {
    if ((Date.now() - _startTime) >= _timeLimitMs) {
      _timeUp = true;
    }
  }

  // ─── Negamax with Alpha-Beta ───────────────────────────────────────────────
  /**
   * Negamax search. Score is always relative to the player to move (positive = good).
   * @param {object} board    - current board state (mutated in-place, restored on return)
   * @param {number} depth    - remaining depth to search
   * @param {number} alpha    - lower bound
   * @param {number} beta     - upper bound
   * @param {number} player   - player to move (P1 or P2)
   * @param {number} ply      - current ply from root (0-based)
   * @returns {number} score from the current player's perspective
   */
  function negamax(board, depth, alpha, beta, player, ply) {
    // Initialize PV length for this ply FIRST (before any early returns)
    pvLength[ply] = ply;

    // Time check every 2048 nodes
    if ((_nodes & 0x7ff) === 0) checkTime();
    if (_timeUp) return 0;

    _nodes++;

    const origAlpha = alpha;

    // ── Transposition table probe ──
    const hashHi = board.hashHi;
    const hashLo = board.hashLo;
    let ttMove = -1;

    if (ttProbe(hashHi, hashLo)) {
      if (_ttResult.depth >= depth) {
        const ttS = _ttResult.score;
        const ttF = _ttResult.flag;
        if (ttF === EXACT) {
          // Store PV from TT if possible
          pvLine[ply][ply] = _ttResult.bestMove;
          pvLength[ply] = ply + 1;
          return ttS;
        }
        if (ttF === LOWER && ttS > alpha) alpha = ttS;
        if (ttF === UPPER && ttS < beta)  beta  = ttS;
        if (alpha >= beta) return ttS;
      }
      ttMove = _ttResult.bestMove;
    }

    // ── Terminal check: did the previous player just win? ──
    if (board.historyTop > 0) {
      const lastCol    = board.history[board.historyTop - 1];
      const lastRow    = board.heights[lastCol] - 1;
      const lastPlayer = player === P1 ? P2 : P1; // opponent just moved
      if (checkWin(board.cells, lastCol, lastRow, lastPlayer)) {
        // Opponent won — return negative score; prefer shorter wins (depth bonus)
        return -(WIN_SCORE + depth);
      }
    }

    // ── Draw check ──
    if (isDraw(board)) return DRAW_SCORE;

    // ── Leaf node — evaluate statically ──
    if (depth === 0) {
      return evaluate(board, player);
    }

    // ── Move generation ──
    const moveBuf  = _moveLists[ply];
    const scoreBuf = _moveScores[ply];
    let moveCount  = generateMoves(board, player, ply, moveBuf, scoreBuf);

    if (moveCount === 0) return DRAW_SCORE;

    // Put TT move first (override ordering) to get best pruning
    if (ttMove >= 0) {
      for (let i = 0; i < moveCount; i++) {
        if (moveBuf[i] === ttMove) {
          const tmp  = moveBuf[i];  moveBuf[i]  = moveBuf[0];  moveBuf[0]  = tmp;
          const tmps = scoreBuf[i]; scoreBuf[i] = scoreBuf[0]; scoreBuf[0] = tmps;
          break;
        }
      }
    }

    let bestScore = -INF;
    let bestMove  = moveBuf[0];

    for (let mi = 0; mi < moveCount; mi++) {
      const col = moveBuf[mi];

      makeMove(board, col);
      const score = -negamax(board, depth - 1, -beta, -alpha, player === P1 ? P2 : P1, ply + 1);
      undoMove(board);

      if (_timeUp) return bestScore === -INF ? 0 : bestScore;

      if (score > bestScore) {
        bestScore = score;
        bestMove  = col;

        // Update PV: this ply's move + child's continuation
        pvLine[ply][ply] = col;
        const childPvEnd = pvLength[ply + 1];
        for (let p = ply + 1; p < childPvEnd; p++) {
          pvLine[ply][p] = pvLine[ply + 1][p];
        }
        pvLength[ply] = childPvEnd;
      }

      if (score > alpha) {
        alpha = score;
      }

      if (alpha >= beta) {
        // Beta cutoff — update killer and history heuristics
        killerStore(ply, col);
        historyUpdate(player, col, depth);
        break;
      }
    }

    // ── Transposition table store ──
    if (!_timeUp) {
      let flag;
      if (bestScore <= origAlpha) flag = UPPER;      // all-node: upper bound
      else if (bestScore >= beta) flag = LOWER;      // cut-node: lower bound
      else                        flag = EXACT;      // PV-node: exact
      ttStore(hashHi, hashLo, depth, bestScore, flag, bestMove);
    }

    return bestScore;
  }

  // ─── Aspiration Window Search ──────────────────────────────────────────────
  /**
   * Search at a given depth with aspiration windows around prevScore.
   * Widens the window on fail-low or fail-high.
   * @returns {{ score: number, bestMove: number }}
   */
  function aspirationSearch(board, depth, player, prevScore) {
    const WINDOW = 500;
    let alpha, beta;

    if (depth <= 2) {
      alpha = -INF;
      beta  =  INF;
    } else {
      alpha = prevScore - WINDOW;
      beta  = prevScore + WINDOW;
    }

    let widened = 0;

    while (true) {
      pvLength[0] = 0;
      const score = negamax(board, depth, alpha, beta, player, 0);

      if (_timeUp) {
        // Return whatever we have so far
        const bm = pvLength[0] > 0 ? pvLine[0][0] : -1;
        return { score, bestMove: bm };
      }

      if (score <= alpha) {
        // Fail-low: widen left window
        widened++;
        alpha = widened >= 3 ? -INF : Math.max(-INF, alpha - WINDOW * (1 << widened));
      } else if (score >= beta) {
        // Fail-high: widen right window
        widened++;
        beta = widened >= 3 ? INF : Math.min(INF, beta + WINDOW * (1 << widened));
      } else {
        // Score within window — success
        const bm = pvLength[0] > 0 ? pvLine[0][0] : -1;
        return { score, bestMove: bm };
      }
    }
  }

  // ─── Public API ────────────────────────────────────────────────────────────

  /**
   * Analyze the position with iterative deepening + aspiration windows.
   *
   * @param {object} boardState   - board from createBoard() with moves applied
   * @param {number} currentPlayer - P1 or P2
   * @param {number} [maxDepth=12] - maximum search depth
   * @param {number} [timeLimitMs=5000] - time budget in milliseconds
   * @returns {{ score: number, bestMove: number, pv: number[], depth: number,
   *             nodes: number, timeMs: number }}
   */
  function analyze(boardState, currentPlayer, maxDepth, timeLimitMs) {
    maxDepth    = (maxDepth    != null) ? maxDepth    : 12;
    timeLimitMs = (timeLimitMs != null) ? timeLimitMs : 5000;

    _nodes       = 0;
    _startTime   = Date.now();
    _timeLimitMs = timeLimitMs;
    _timeUp      = false;

    ttClear();
    historyReset();
    killers.fill(-1);

    // Pick a fallback move immediately (first valid center-preferred column)
    let bestMove  = -1;
    for (let oi = 0; oi < COLS; oi++) {
      const col = COL_ORDER[oi];
      if (isValidMove(boardState, col)) { bestMove = col; break; }
    }

    let bestScore    = 0;
    let bestPv       = bestMove >= 0 ? [bestMove] : [];
    let reachedDepth = 0;
    let prevScore    = 0;

    // Iterative deepening loop
    for (let depth = 1; depth <= maxDepth; depth++) {
      pvLength.fill(0);

      const result = aspirationSearch(boardState, depth, currentPlayer, prevScore);

      if (_timeUp && depth > 1) break; // incomplete search at this depth — discard

      // Accept this depth's result
      bestScore = result.score;
      if (result.bestMove >= 0 && result.bestMove < COLS) {
        bestMove = result.bestMove;
      }

      // Extract PV from pvLine[0]
      bestPv = [];
      const pvEnd = pvLength[0];
      for (let p = 0; p < pvEnd; p++) {
        bestPv.push(pvLine[0][p]);
      }
      if (bestPv.length === 0 && bestMove >= 0) {
        bestPv = [bestMove];
      }

      reachedDepth = depth;
      prevScore    = bestScore;

      // If a forced win or loss is found, no need to search deeper
      if (Math.abs(bestScore) >= WIN_SCORE / 2) break;
    }

    return {
      score:    bestScore,
      bestMove: bestMove,
      pv:       bestPv,
      depth:    reachedDepth,
      nodes:    _nodes,
      timeMs:   Date.now() - _startTime,
    };
  }

  /**
   * Get the best column index to play.
   *
   * @param {object} boardState
   * @param {number} currentPlayer
   * @param {number} [maxDepth=12]
   * @param {number} [timeLimitMs=5000]
   * @returns {number} column index (0-8)
   */
  function getBestMove(boardState, currentPlayer, maxDepth, timeLimitMs) {
    return analyze(boardState, currentPlayer, maxDepth, timeLimitMs).bestMove;
  }

  // ─── Export ────────────────────────────────────────────────────────────────
  global.Connect5Engine = {
    // Board helpers
    createBoard,
    cloneBoard,
    makeMove,
    undoMove,
    isValidMove,
    getWinner,
    isDraw,

    // AI
    analyze,
    getBestMove,

    // Threat analysis
    countThreats,

    // Constants
    COLS,
    ROWS,
    P1,
    P2,
    EMPTY,
    WIN_SCORE,
  };

})(typeof window !== 'undefined' ? window : global);
