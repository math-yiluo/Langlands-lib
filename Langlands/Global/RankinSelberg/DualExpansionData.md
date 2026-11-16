# Dual Whittaker-type functions and their corner sums

Module `Langlands.Global.RankinSelberg.DualExpansionData`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`.

Provenance: internal. The axioms of `DualData` are the properties of the dual Whittaker
function `W̃ = dualFunction W` used in the dual unfolding (Cogdell 2004, §2.2): left
`N(𝔸)`-equivariance by the inverse generic character, and a Whittaker expansion over
`N_(m+K)(F) \ GL_(m+K)(F)` with locally uniform absolute convergence.

## Definitions

- `cornerFamily F m K W q g = W(diag(q.out, 1) · g)` for `q ∈ N_(m+K)(F) \ GL_(m+K)(F)`,
  `cornerSum` its sum and `cornerNormSum` the sum of norms.
- `DualData F m ψ K W` (structure): `W` is continuous on `GL_(m+K+1)(𝔸)`, satisfies
  `W(n g) = ψ_N(n)⁻¹ W(g)` for `n ∈ N_(m+K+1)(𝔸)` with `ψ_N = genericCharacter F (m+K) ψ 1`,
  and `cornerFamily` is `LocUnifSummable`.
- `dualPullback W y h = W(diag(h, 1) · y)`, a function on `GL_(m+K+1)(𝔸)` from one on
  `GL_(m+K+2)(𝔸)`.

## Results

- `DualData.padRational_of_rightRel`: `W(diag(a, I) z)` depends only on `N(F) a`.
- Invariance of `cornerSum`/`cornerNormSum` under `diag(GL_(m+K)(F), 1)` (via the right action
  `cosetMulEquiv` on cosets) and under rational last-column points (`DualData.lastColPoint_mul`,
  which uses `padRational_mul_lastColPoint`).
- Continuity of the corner sums (`DualData.continuous_cornerSum`, `continuous_cornerNormSum`)
  and `norm_cornerSum_le`.
- `DualData.pullbackData`: the pullback of a `DualData` function on rank `m+K+2` along
  `diag(·, 1) · y` is a `DualData` function on rank `m+K+1`; its corner family is a subfamily of
  the original one along `cosetPad` (`DualData.cornerFamily_dualPullback`).
