# Convergence of the Jacquet integrals at the torus points

Module `Langlands.Representation.Shahidi.OpenCellJacquetConvergence`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

- `exists_norm_satakeSchur_le`: for fixed `x` there are `C ≥ 0`, `R ≥ 1` with
  `‖s_ρ(x)‖ ≤ C R^(∑ |ρ_i|)` for all antitone `ρ`; `exists_norm_sphericalWhittaker_le`: for an
  integrally trivial unitary character `θ` and `q ≥ 1`, likewise
  `‖W°(u ϖ^ρ; x)‖ ≤ C R^(∑ |ρ_i|)` for all upper unipotent `u` and all `ρ`.
- `sphericalWhittaker_smul_unipotent_mul_torus`: for an integrally trivial `θ`, homogeneity
  `W°(u ϖ^ρ; X x) = X^(∑ ρ_i) W°(u ϖ^ρ; x)`.
- `blockWeyl_mul_intertwiningUnipotent_mul_swap`: `w u'(Y) diag'(h₂, h₁) =
  diag(h₁, h₂) w u'(h₂⁻¹ Y h₁)`; `translatedLower`, and for a Levi-invariant `Φ`
  `jacquetIntegrandAt_swap`, `isLatticePeriodic_translatedLower`, `translatedLower_eq`.
- `twoBlockModulus_unipotent_mul_torus`, `norm_fullΦ_unipotent_mul_torus`,
  `norm_translatedLower_fullΦ_le` (for `ψ` of conductor `𝒪`): bounds for the section's Levi
  function along the open cell.
- `integrable_of_isLatticePeriodic_of_depth_bound`: a lattice-periodic function bounded by
  `C ρ^(depth)` with `C, ρ ≥ 0` is integrable when `q^((t+1)(r+1)) ρ < 1`.
- `torus_eq_swapRank_blockSum`: every torus point is an exchanged block torus point.
- `exists_integrable_jacquetIntegrandAt_fullΦ`: for `ψ` of conductor `𝒪` and fixed `(a, c, s)`
  there is `r₀ > 0` such that for `‖X‖ < r₀` the Jacquet integrand of the section with
  parameters `(X a, c, s)` is integrable at every torus point.

## Provenance

Derived estimates; the homogeneity in `X` gives decay in the depth.
