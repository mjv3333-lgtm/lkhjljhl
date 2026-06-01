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
  const UPPER = 2; // upper bound (fail-low / alpha cut)

  const INF = 10000000;
  const WIN_SCORE = 5000000;
  const DRAW_SCORE = 0;

  // ─── Column order for move ordering (center-first) ────────────────────────
  // Pre-sorted center-preferred column order: 4,3,5,2,6,1,7,0,8
  const COL_ORDER = new Int32Array([4, 3, 5, 2, 6, 1, 7, 0, 8]);

  // ─── Zobrist Hashing (64-bit emulated with two 32-bit halves) ─────────────
  // Tables: zobrist[player-1][col][row] = {hi, lo}
  // player index 0 = P1, 1 = P2
  const zobristHi = new Uint32Array(2 * COLS * ROWS);
  const zobristLo = new Uint32Array(2 * COLS * ROWS);

  function zobristIndex(player, col, row) {
    // player: 1 or 2 => index 0 or 1
    return (player - 1) * COLS * ROWS + col * ROWS + row;
  }

  (function initZobrist() {
    // Simple LCG PRNG for deterministic initialization
    let seed = 0xdeadbeef;
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
  // Precomputed bonus for each cell based on distance from center.
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
      heights: new Int32Array(COLS),   // next available row index per column
      moveCount: 0,
      history: new Int32Array(SIZE),   // stack of columns played
      historyTop: 0,
      hashHi: 0,
      hashLo: 0,
    };
  }

  /** Clone a board for external use (not used in hot path). */
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

  // Inline index helpers
  function idx(col, row) {
    return col * ROWS + row;
  }

  /**
   * Make a move for the current player (determined externally).
   * Returns false if column is full or invalid.
   */
  function makeMove(board, col) {
    if (col < 0 || col >= COLS) return false;
    const row = board.heights[col];
    if (row >= ROWS) return false;

    // Determine current player from moveCount: odd moves = P2, even = P1
    const player = (board.moveCount & 1) === 0 ? P1 : P2;
    const i = idx(col, row);

    board.cells[i] = player;
    board.heights[col] = row + 1;
    board.history[board.historyTop++] = col;
    board.moveCount++;

    // Update hash
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

    // Undo hash
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
   * Checks 4 directions: horizontal, vertical, diag1 (↗), diag2 (↘).
   * Only examines up to 4 cells in each direction from the placed piece.
   * O(1) — bounded to 8 cells per direction.
   */
  const DIRS = [
    [1, 0],   // horizontal
    [0, 1],   // vertical
    [1, 1],   // diagonal ↗
    [1, -1],  // diagonal ↘
  ];

  function checkWin(cells, col, row, player) {
    for (let d = 0; d < 4; d++) {
      const dc = DIRS[d][0];
      const dr = DIRS[d][1];
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
   * Determine the winner of the board by scanning the last move.
   * Returns P1, P2, or 0 (no winner).
   */
  function getWinner(board) {
    if (board.historyTop === 0) return 0;
    const col = board.history[board.historyTop - 1];
    const row = board.heights[col] - 1;
    const player = ((board.moveCount - 1) & 1) === 0 ? P1 : P2;
    if (checkWin(board.cells, col, row, player)) return player;
    return 0;
  }

  function isDraw(board) {
    return board.moveCount >= SIZE;
  }

  // ─── Evaluation ────────────────────────────────────────────────────────────
  /**
   * Score a window of 5 cells for player p relative to the evaluating side.
   * Returns a partial score contribution.
   */
  function scoreWindow5(cells, positions, player, opponent) {
    let pCount = 0, oCount = 0, eCount = 0;
    for (let k = 0; k < 5; k++) {
      const v = cells[positions[k]];
      if (v === player) pCount++;
      else if (v === opponent) oCount++;
      else eCount++;
    }
    if (oCount > 0 && pCount > 0) return 0; // blocked window

    if (pCount === 5) return WIN_SCORE;
    if (pCount === 4 && eCount === 1) return 10000;
    if (pCount === 3 && eCount === 2) return 500;
    if (pCount === 2 && eCount === 3) return 50;
    return 0;
  }

  // Pre-allocated window index buffer to avoid allocations
  const _winBuf = new Int32Array(5);

  /**
   * Evaluate the board from `player`'s perspective.
   */
  function evaluate(board, player) {
    const cells = board.cells;
    const opponent = player === P1 ? P2 : P1;
    let score = 0;

    // Positional bonus
    for (let c = 0; c < COLS; c++) {
      for (let r = 0; r < board.heights[c]; r++) {
        const v = cells[idx(c, r)];
        if (v === player) score += posBonus[c * ROWS + r];
        else if (v === opponent) score -= posBonus[c * ROWS + r];
      }
    }

    let pOpenFours = 0;
    let oOpenFours = 0;

    // Horizontal windows
    for (let r = 0; r < ROWS; r++) {
      for (let c = 0; c <= COLS - WIN_LENGTH; c++) {
        for (let k = 0; k < 5; k++) _winBuf[k] = idx(c + k, r);
        const ps = scoreWindow5(cells, _winBuf, player, opponent);
        const os = scoreWindow5(cells, _winBuf, opponent, player);
        score += ps - os;
        if (ps === 10000) pOpenFours++;
        if (os === 10000) oOpenFours++;
      }
    }

    // Vertical windows
    for (let c = 0; c < COLS; c++) {
      for (let r = 0; r <= ROWS - WIN_LENGTH; r++) {
        for (let k = 0; k < 5; k++) _winBuf[k] = idx(c, r + k);
        const ps = scoreWindow5(cells, _winBuf, player, opponent);
        const os = scoreWindow5(cells, _winBuf, opponent, player);
        score += ps - os;
        if (ps === 10000) pOpenFours++;
        if (os === 10000) oOpenFours++;
      }
    }

    // Diagonal ↗ windows
    for (let c = 0; c <= COLS - WIN_LENGTH; c++) {
      for (let r = 0; r <= ROWS - WIN_LENGTH; r++) {
        for (let k = 0; k < 5; k++) _winBuf[k] = idx(c + k, r + k);
        const ps = scoreWindow5(cells, _winBuf, player, opponent);
        const os = scoreWindow5(cells, _winBuf, opponent, player);
        score += ps - os;
        if (ps === 10000) pOpenFours++;
        if (os === 10000) oOpenFours++;
      }
    }

    // Diagonal ↘ windows
    for (let c = 0; c <= COLS - WIN_LENGTH; c++) {
      for (let r = WIN_LENGTH - 1; r < ROWS; r++) {
        for (let k = 0; k < 5; k++) _winBuf[k] = idx(c + k, r - k);
        const ps = scoreWindow5(cells, _winBuf, player, opponent);
        const os = scoreWindow5(cells, _winBuf, opponent, player);
        score += ps - os;
        if (ps === 10000) pOpenFours++;
        if (os === 10000) oOpenFours++;
      }
    }

    // Double-threat bonus: two open fours for player
    if (pOpenFours >= 2) score += 50000;
    if (oOpenFours >= 2) score -= 50000;

    return score;
  }

  // ─── Transposition Table ───────────────────────────────────────────────────
  // Stored as plain Map with composite key string.
  // Entry: { depth, score, flag, bestMove }
  // We use a fixed-size object pool to reduce GC pressure.
  const TT_SIZE = 1 << 20; // ~1M entries
  const ttDepth   = new Int32Array(TT_SIZE);
  const ttScore   = new Int32Array(TT_SIZE);
  const ttFlag    = new Uint8Array(TT_SIZE);
  const ttBestMove = new Int32Array(TT_SIZE);
  const ttHi      = new Uint32Array(TT_SIZE);  // stored hash hi to verify
  const ttLo      = new Uint32Array(TT_SIZE);  // stored hash lo to verify
  const ttValid   = new Uint8Array(TT_SIZE);   // 1 if slot occupied

  function ttClear() {
    ttValid.fill(0);
  }

  function ttIndex(hashHi, hashLo) {
    // Mix hi and lo to get bucket index
    return ((hashHi ^ (hashLo * 0x9e3779b9)) >>> 0) % TT_SIZE;
  }

  function ttStore(hashHi, hashLo, depth, score, flag, bestMove) {
    const idx2 = ttIndex(hashHi, hashLo);
    // Always-replace strategy
    ttHi[idx2] = hashHi;
    ttLo[idx2] = hashLo;
    ttDepth[idx2] = depth;
    ttScore[idx2] = score;
    ttFlag[idx2] = flag;
    ttBestMove[idx2] = bestMove;
    ttValid[idx2] = 1;
  }

  // Returns true and fills out the shared retrieval object if hit.
  const _ttResult = { depth: 0, score: 0, flag: 0, bestMove: -1 };

  function ttProbe(hashHi, hashLo) {
    const idx2 = ttIndex(hashHi, hashLo);
    if (!ttValid[idx2]) return false;
    if (ttHi[idx2] !== hashHi || ttLo[idx2] !== hashLo) return false;
    _ttResult.depth = ttDepth[idx2];
    _ttResult.score = ttScore[idx2];
    _ttResult.flag  = ttFlag[idx2];
    _ttResult.bestMove = ttBestMove[idx2];
    return true;
  }

  // ─── Killer Heuristic ──────────────────────────────────────────────────────
  // 2 killer slots per ply, up to MAX_DEPTH plies
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
  // history[player-1][col]
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
  // Pre-allocated move score and move arrays per ply
  const _moveLists = [];
  const _moveScores = [];
  for (let i = 0; i < MAX_DEPTH + 2; i++) {
    _moveLists.push(new Int32Array(COLS));
    _moveScores.push(new Int32Array(COLS));
  }

  /**
   * Check if column `col` leads to an immediate win for `player` on `board`.
   */
  function isImmediateWin(board, col, player) {
    const row = board.heights[col];
    if (row >= ROWS) return false;
    // Temporarily place
    board.cells[idx(col, row)] = player;
    const win = checkWin(board.cells, col, row, player);
    board.cells[idx(col, row)] = EMPTY;
    return win;
  }

  /**
   * Generate and order moves for the current position.
   * Returns the number of valid moves; fills moveBuf.
   */
  function generateMoves(board, player, ply, moveBuf, scoreBuf) {
    const opponent = player === P1 ? P2 : P1;
    let count = 0;

    for (let oi = 0; oi < COLS; oi++) {
      const col = COL_ORDER[oi];
      if (!isValidMove(board, col)) continue;

      let score = 0;

      // 1. Immediate win
      if (isImmediateWin(board, col, player)) {
        score = 100000000;
      }
      // 2. Block opponent immediate win
      else if (isImmediateWin(board, col, opponent)) {
        score = 90000000;
      }
      // 3. Killer move
      else if (isKiller(ply, col)) {
        score = 80000000;
      }
      // 4. History heuristic
      else {
        score = historyScore(player, col) + (4 - Math.abs(col - 4)) * 1000;
      }

      moveBuf[count] = col;
      scoreBuf[count] = score;
      count++;
    }

    // Sort descending by score (insertion sort — small N)
    for (let i = 1; i < count; i++) {
      const mv = moveBuf[i], sc = scoreBuf[i];
      let j = i - 1;
      while (j >= 0 && scoreBuf[j] < sc) {
        moveBuf[j + 1] = moveBuf[j];
        scoreBuf[j + 1] = scoreBuf[j];
        j--;
      }
      moveBuf[j + 1] = mv;
      scoreBuf[j + 1] = sc;
    }

    return count;
  }

  // ─── Principal Variation Storage ───────────────────────────────────────────
  // pvTable[ply] stores the best move at that ply for pv reconstruction
  const pvTable = new Int32Array(MAX_DEPTH + 2).fill(-1);
  const pvLength = new Int32Array(MAX_DEPTH + 2);
  // Full PV line per ply: pvLine[ply][...] = sequence of moves
  const pvLine = [];
  for (let i = 0; i < MAX_DEPTH + 2; i++) {
    pvLine.push(new Int32Array(MAX_DEPTH + 2));
  }

  // ─── Search State ──────────────────────────────────────────────────────────
  let _nodes = 0;
  let _startTime = 0;
  let _timeLimitMs = 5000;
  let _timeUp = false;
  let _searchPlayer = P1; // the player who called analyze()

  function checkTime() {
    if ((Date.now() - _startTime) >= _timeLimitMs) {
      _timeUp = true;
    }
  }

  // ─── Negamax with Alpha-Beta ───────────────────────────────────────────────
  /**
   * Negamax search. Score is always relative to the player to move.
   * @param {object} board
   * @param {number} depth  remaining depth
   * @param {number} alpha
   * @param {number} beta
   * @param {number} player  player to move (P1 or P2)
   * @param {number} ply     current ply from root
   */
  function negamax(board, depth, alpha, beta, player, ply) {
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
        if (ttF === EXACT) return ttS;
        if (ttF === LOWER && ttS > alpha) alpha = ttS;
        if (ttF === UPPER && ttS < beta) beta = ttS;
        if (alpha >= beta) return ttS;
      }
      ttMove = _ttResult.bestMove;
    }

    // ── Terminal check ──
    // Did the last move win?
    if (board.historyTop > 0) {
      const lastCol = board.history[board.historyTop - 1];
      const lastRow = board.heights[lastCol] - 1;
      const lastPlayer = player === P1 ? P2 : P1; // opponent just moved
      if (checkWin(board.cells, lastCol, lastRow, lastPlayer)) {
        // opponent won, that's bad for the current player
        return -(WIN_SCORE + depth); // prefer shorter wins
      }
    }

    if (isDraw(board)) return DRAW_SCORE;

    // ── Leaf node ──
    if (depth === 0) {
      return evaluate(board, player);
    }

    // ── Move generation ──
    const moveBuf = _moveLists[ply];
    const scoreBuf = _moveScores[ply];
    let moveCount = generateMoves(board, player, ply, moveBuf, scoreBuf);

    if (moveCount === 0) return DRAW_SCORE;

    // Put TT move first if valid
    if (ttMove !== -1) {
      for (let i = 0; i < moveCount; i++) {
        if (moveBuf[i] === ttMove) {
          // Swap to front
          const tmp = moveBuf[i]; moveBuf[i] = moveBuf[0]; moveBuf[0] = tmp;
          const tmps = scoreBuf[i]; scoreBuf[i] = scoreBuf[0]; scoreBuf[0] = tmps;
          break;
        }
      }
    }

    let bestScore = -INF;
    let bestMove = moveBuf[0];
    pvLength[ply] = ply; // reset pv length for this ply

    for (let mi = 0; mi < moveCount; mi++) {
      const col = moveBuf[mi];

      makeMove(board, col);
      const score = -negamax(board, depth - 1, -beta, -alpha, player === P1 ? P2 : P1, ply + 1);
      undoMove(board);

      if (_timeUp) return bestScore;

      if (score > bestScore) {
        bestScore = score;
        bestMove = col;
        // Update PV
        pvLine[ply][ply] = col;
        for (let p = ply + 1; p < pvLength[ply + 1]; p++) {
          pvLine[ply][p] = pvLine[ply + 1][p];
        }
        pvLength[ply] = pvLength[ply + 1];
      }

      if (score > alpha) {
        alpha = score;
      }

      if (alpha >= beta) {
        // Beta cutoff — store killer and history
        killerStore(ply, col);
        historyUpdate(player, col, depth);
        break;
      }
    }

    // ── TT store ──
    if (!_timeUp) {
      const flag = bestScore <= origAlpha ? UPPER : bestScore >= beta ? LOWER : EXACT;
      ttStore(hashHi, hashLo, depth, bestScore, flag, bestMove);
    }

    return bestScore;
  }

  // ─── Aspiration Window Search ──────────────────────────────────────────────
  /**
   * Search at a given depth with aspiration windows.
   * Returns { score, bestMove }.
   */
  function aspirationSearch(board, depth, player, prevScore) {
    const WINDOW = 500;
    let alpha = depth > 2 ? prevScore - WINDOW : -INF;
    let beta  = depth > 2 ? prevScore + WINDOW : INF;

    while (true) {
      pvLength[0] = 0;
      const score = negamax(board, depth, alpha, beta, player, 0);

      if (_timeUp) return { score, bestMove: pvLine[0][0] !== undefined ? pvLine[0][0] : -1 };

      if (score <= alpha) {
        // Fail low — widen left
        alpha = alpha <= -INF + WINDOW ? -INF : alpha - WINDOW * 4;
      } else if (score >= beta) {
        // Fail high — widen right
        beta = beta >= INF - WINDOW ? INF : beta + WINDOW * 4;
      } else {
        return { score, bestMove: pvLine[0][0] };
      }
    }
  }

  // ─── Public API ────────────────────────────────────────────────────────────

  /**
   * Analyze the position with iterative deepening + aspiration windows.
   * @param {object} boardState   board from createBoard() with moves applied
   * @param {number} currentPlayer  P1 or P2
   * @param {number} maxDepth       max search depth (default 12)
   * @param {number} timeLimitMs    time budget in ms (default 5000)
   * @returns {{ score, bestMove, pv, depth, nodes, timeMs }}
   */
  function analyze(boardState, currentPlayer, maxDepth, timeLimitMs) {
    maxDepth = maxDepth || 12;
    timeLimitMs = timeLimitMs || 5000;

    _nodes = 0;
    _startTime = Date.now();
    _timeLimitMs = timeLimitMs;
    _timeUp = false;
    _searchPlayer = currentPlayer;

    ttClear();
    historyReset();
    killers.fill(-1);
    pvLength.fill(0);

    let bestMove = -1;
    let bestScore = 0;
    let bestPv = [];
    let reachedDepth = 0;
    let prevScore = 0;

    // Pick a fallback move immediately (first valid center-preferred col)
    for (let oi = 0; oi < COLS; oi++) {
      const col = COL_ORDER[oi];
      if (isValidMove(boardState, col)) {
        bestMove = col;
        break;
      }
    }

    // Iterative deepening
    for (let depth = 1; depth <= maxDepth; depth++) {
      pvLength.fill(0);

      const result = aspirationSearch(boardState, depth, currentPlayer, prevScore);

      if (_timeUp && depth > 1) break;

      if (!_timeUp || depth === 1) {
        bestScore = result.score;
        if (result.bestMove !== -1 && result.bestMove !== undefined) {
          bestMove = result.bestMove;
        }
        // Extract PV
        bestPv = [];
        for (let p = 0; p < pvLength[0]; p++) {
          bestPv.push(pvLine[0][p]);
        }
        reachedDepth = depth;
        prevScore = bestScore;
      }

      // If we found a forced win/loss, no need to go deeper
      if (Math.abs(bestScore) >= WIN_SCORE / 2) break;
    }

    return {
      score: bestScore,
      bestMove,
      pv: bestPv,
      depth: reachedDepth,
      nodes: _nodes,
      timeMs: Date.now() - _startTime,
    };
  }

  /**
   * Get the best column index to play.
   * @param {object} boardState
   * @param {number} currentPlayer
   * @param {number} maxDepth
   * @param {number} timeLimitMs
   * @returns {number} column index
   */
  function getBestMove(boardState, currentPlayer, maxDepth, timeLimitMs) {
    const result = analyze(boardState, currentPlayer, maxDepth, timeLimitMs);
    return result.bestMove;
  }

  // ─── Export ────────────────────────────────────────────────────────────────
  global.Connect5Engine = {
    // Core game helpers
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

    // Constants
    COLS,
    ROWS,
    P1,
    P2,
    EMPTY,
    WIN_SCORE,
  };

})(typeof window !== 'undefined' ? window : global);
