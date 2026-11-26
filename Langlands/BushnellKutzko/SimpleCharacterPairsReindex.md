# Simple character pairs at a changed first index

A simple stratum `[𝔄,n,r,β]` is also simple at every smaller index, and at
every larger index below `−k₀(β,𝔄)`. This module shows that the sets
`simpleCharacterPairs ψF S m` of subgroup–character pairs do not depend on
which simple index `r` the stratum carries.

- `simpleCriticalDepth_gt_of_criticalExponent_lt`: if `k₀(β,𝔄) < −r`, then
  `r < simpleCriticalDepth L β`. This includes the case `k₀ = −∞`.
- `criticalExponent_lt_succ_of_ne`: if `k₀(β,𝔄) < −m` and
  `k₀(β,𝔄) ≠ −(m+1)`, then `k₀(β,𝔄) < −(m+1)`.
- `Stratum.DefiningSequenceChoice.reindex`: let `S` and `S'` be strata with the
  same chain, level and element, and let `S'` be simple. The construction turns
  a defining sequence of `S` (BK93 (2.4.2)) into one of `S'`. It changes only the
  index of the first term, to `S'.r`. The first element and all later terms are
  kept, so `reindex_tail` states that the tail is unchanged. The new first index
  is below the second index of the sequence, `−k₀(β,𝔄)`, because `S'` is simple.
- `simpleCharacterPairs_congr`: two simple strata with the same chain, level
  and element have the same pairs at every depth `m`. Reindexing defining
  sequences in both directions preserves the tails, and the pairs depend only on
  the chain, the level, the element and the tail.

BK93 §3.2 fixes a simple stratum `[𝔄,n,0,β]` and defines `C(𝔄,m,β)` for each
depth `m ≥ 0` in (3.2.1) and (3.2.3). The depth `m` is the only index that
enters, so the set does not depend on an index of the stratum. Source: Bushnell
and Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993),
(2.4.2), printed pp. 65–66, and §3.2, (3.2.1)–(3.2.3), printed pp. 98–99,
literature ID `bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
