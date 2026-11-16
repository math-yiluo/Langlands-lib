# The column step of the dual period

Module `Langlands.Global.RankinSelberg.DualExpansionStep`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`.

Provenance: internal. This is the analytic core of one step of the rank induction for the dual
expansion: integrating the last column against `ψ(last entry)` keeps the cosets whose last row is
standard on the middle block, and these are reindexed by `N_(m+K)(F) \ GL_(m+K)(F) × F^m`.

- `numberFieldCountable`: number fields are countable (instance).
- `DualData.torusIntegral_cornerSum_col` (orthogonality): the column integral
  `T_c ψ(lastEntry c) cornerSum (K+1) W (x̂ ĉ z)` is the sum of `cornerFamily q (x̂ z)` over the
  cosets `q` with `SurvivorRow`. It uses `DualData.cornerFamily_xcPoint` (the effect of the column
  on each corner term is the character `pairChar ψ (survivorCoeff q)`) and
  `torusIntegral_pairChar`.
- `tsum_survivorRow_eq` reindexes the surviving cosets by `survivorMap`, and
  `DualData.cornerFamily_survivorMap` rewrites each surviving term as a corner term of the
  pullback `dualPullback W y` at rank `m+K+1`.
- `DualData.torusIntegral_col_eq_pullback`: combining the previous results, the column integral is
  `Σ_(β ∈ F^m) cornerSum K (dualPullback W y) (x̂' · rowPoint(b + β) · h)`.
- `rectSplit`, `joinRect` and `torusIntegral_rect_succ`: splitting a rectangle on `K + 1` rows
  into its first `K` rows and its last row, for torus integrals.
- `xcPoint_rowPoint_shift`, `DualData.isPeriodic_rect`, `DualData.isPeriodic_col`,
  `midPoint_colHom_padHom`: point identities and periodicity of the corner sums.
- `DualData.summable_norm_col` and `DualData.rowJ_bound`: domination of the sums over `β`.
- `DualData.torusIntegral_rect_col`: the rectangle-and-column integral at rank `K + 1`, for fixed
  `u`, `c'` and last row `b`, is `Σ_β T_(x') cornerSum K (dualPullback W y)
  (x̂' ĉ' · diag(I,u,1) · rowPoint(b + β))`.
