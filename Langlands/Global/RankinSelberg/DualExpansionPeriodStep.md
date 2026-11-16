# The period step of the dual expansion

Module `Langlands.Global.RankinSelberg.DualExpansionPeriodStep`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`.

Provenance: internal.

## Definitions

- `rowJ V u c' b' = T_(x') cornerSum K V (x̂' ĉ' · diag(I, u, 1) · rowPoint b')`.
- `colPsi ψ W y u c' b = T_(x') rectInner_(K+1) (cornerSum (K+1) W)
  (diag(x̂(0) ĉ' diag(I,u,1), 1) · y) (joinRect x' b)`: the rank-`K+1` rectangle-and-column integral
  with the last row `b` fixed.

## Results

- Continuity and periodicity of `rowJ` and `colPsi` (`DualData.continuous_rowJ`,
  `DualData.isPeriodic_rowJ`, `DualData.continuous_colPsi`, `DualData.isPeriodic_colPsi_col`,
  `DualData.isPeriodic_colPsi_row`), the identity `DualData.colPsi_eq_tsum`
  (`colPsi = Σ_β rowJ (dualPullback W y) u c' (b + β)`), and uniform bounds
  (`DualData.exists_rowJ_bound`, `DualData.norm_colPsi_le`).
- `superSum_rational_char`: `ψ(superSum g) = 1` for `g ∈ N_K(F)`.
- `DualData.dualPeriod_eq_rowJ`: the dual period at a row point in terms of `rowJ`.
- `DualData.dualPeriod_succ_col`: the last-column decomposition (`unipotentPeriod_succ`) applied
  to the dual period at rank `K + 1`, with the rectangle period split along its last row.
- `DualData.colStep_swap` and `DualData.periodStep_row`: exchange of the column, last-row and
  unipotent integrations and of the sum over `β`, justified by continuity, periodicity and the
  uniform bounds.
- **`DualData.dualPeriod_succ`**: for a `DualData` function `W` at rank `m + K + 2`,
  `dualPeriod (K+1) W y = T_(b ∈ (𝔸/F)^m) Σ_(β ∈ F^m) dualPeriod K (dualPullback W y)
  (rowPoint (b + β))`.
