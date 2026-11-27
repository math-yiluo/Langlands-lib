# The linear part of the twisted chart over a cyclic extension

Module `Langlands.BaseChange.TwistedLocalDescent.ChartLinear`. Let `E/F` be fields, `σ` an
`F`-automorphism of `E`, `B` a block shape and `m ∈ M(E)`.

- `lowerPartLinear B`: the strictly block lower part, as an `F`-linear map;
  `chartLinear B σ m X = X_𝔭 + T(X_𝔲̄)` with `T = twistedOperator B σ m = σ − Ad(m)⁻¹`.
- `det_chartLinear` (for `E/F` finite): `det_F(chartLinear) = det_F(T | 𝔲̄)`. The map preserves
  `𝔲̄`, where it is `T`, and induces the identity on `M_n/𝔲̄` (`LinearMap.det_eq_det_mul_det`).

For nonarchimedean local fields `E/F` with `E` a cyclic algebra of group `⟨σ⟩`:

- `det_chartLinear_ne_zero`: if `D_{G/M,σ}(m) ≠ 0`, then `det_F(chartLinear) ≠ 0` (by
  `residueNormalizedAbsoluteValue_det_twistedOperator_sq`).
- `chartLinearEquiv`: the map as a continuous `F`-linear automorphism of `M_n(E)` (continuity of
  `F`-linear maps for the module topology, `matrix_isModuleTopology`); `chartLinearEquiv_apply`.
- `map_chartLinearEquiv`: it scales additive Haar measure by `|det_F|_F⁻¹`
  (`map_linearEquiv_residueAbsolute`).
- `sqrt_leviModulus_mul_inv_det_chartLinear` (**weight identity**):
  `δ_P(m)^{1/2} · |det_F(chartLinear)|_F⁻¹ = |D_{G/M,σ}(m)|_F^{-1/2}` (from
  `|det_F(T | 𝔲̄)|² = |D_{G/M,σ}(m)| · δ_P(m)`; both sides are `0` when `D = 0`).

With the local norm `LocalGalois.localNormedField E` on `E` and the sup norm on matrices:

- `chartLinear_eq_twistedChartLinear`: `chartLinear B σ m` is the linear part
  `twistedChartLinear B σ m m⁻¹` of the twisted chart at `m`.
- `exists_norm_symm_chartLinearEquiv_le`: its inverse is bounded, `‖A⁻¹ Y‖ ≤ C ‖Y‖`
  (`exists_norm_le_of_continuous_of_map_smul` with a scalar of `F` of norm `> 1`).
