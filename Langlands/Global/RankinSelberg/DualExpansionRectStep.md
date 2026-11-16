# The rectangular side of the dual expansion and its rank step

Module `Langlands.Global.RankinSelberg.DualExpansionRectStep`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`.

Provenance: internal.

## Cosets

- `rectRat_apply`: the entries of `diag(p, I) · x̂_B` in `GL_(m+K)(F)`.
- `rectCoset (p, B) = N(F) · diag(p.out, I) · x̂_B` and **`rectCoset_injective`**: distinct
  `(N_m(F) p, B) ∈ N_m(F) \ GL_m(F) × F^(K×m)` give distinct cosets in
  `N_(m+K)(F) \ GL_(m+K)(F)`. The proof compares the columns `m, …` and the rows `m, …` of the two
  representatives.

## The unfolded side

- `rectFamily K W y X (p, B) = W(diag(p.out, I) · x̂_(X+B) · y)`. By
  `DualData.rectFamily_eq` it is the corner term of `rectCoset (p, B)` at `x̂_X y`, so the family
  is locally uniformly absolutely summable with sum of norms bounded by the corner norm sum
  (`DualData.locUnifSummable_rectFamily`, `DualData.tsum_norm_rectFamily_le`,
  `DualData.exists_rectFamily_bound`), continuous and periodic in `X`.
- `dualRectT K W y = T_X Σ_(p, B) rectFamily K W y X (p, B)`.
- `DualData.dualRectT_succ`: the same step as `DualData.dualPeriod_succ`:
  `dualRectT (K+1) W y = T_b Σ_β dualRectT K (dualPullback W y) (rowPoint (b + β))`, using
  `rectFamily_succ` and the reindexing `rectSplitEquiv`.
- Base cases: `dualRectT_zero` and `dualPeriod_zero` (both are the corner sum at `K = 0`).
- **`dualPeriod_eq_dualRectT`**: by induction on `K`, for every `DualData` function `W` and every
  `y`, `dualPeriod F m K ψ W y = dualRectT K W y`, for `ψ` continuous, of norm one, trivial on
  `F`, and such that for every `a ≠ 0` in `F` some `y` has `ψ(a y) ≠ 1`.
