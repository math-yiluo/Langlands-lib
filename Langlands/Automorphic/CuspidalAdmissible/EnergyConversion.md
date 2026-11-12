# From the energy to band integrals of derivatives

Module: `Langlands.Automorphic.CuspidalAdmissible.EnergyConversion`. Provenance: internal.

## Inner product cores

For a Hermitian form given as `InnerProductSpace.Core ℂ V` (the norm is built locally from the
core):

- `re_inner_sum_smul_le_core`: `re c(∑ a_i v_i, ∑ a_i v_i) ≤ (∑ a_i²) ∑ re c(v_i, v_i)` for
  real `a_i` (triangle inequality and `Finset.sum_mul_sq_le_sq_mul_sq`).
- `eq_zero_of_re_inner_self_le_zero_core`: `re c(x, x) ≤ 0` implies `x = 0`.

## Band integrals

- `ofReal_re_integral_inner_self`: for `φ ∈ L²(μ)` with complex values,
  `re ∫ ⟨φ, φ⟩ dμ = ∫ |φ|² dμ` (as extended reals).
- `bandNorm_eq_ofReal_inner`: for the band unitary form `unitaryForm F n S hn hS χ hχ hSχ hL2`
  (Library, `unitaryForm_inner`), `bandNorm S f = re b(f, f)`.

## Derivatives and energy

- `cartanCoord k i`: the real coordinates of the basis direction `lieDirection k` in the
  normalized Cartan basis `cartanAdaptedBasis`.
- `basisDerivative_eq_sum`: `D_k f = ∑_i cartanCoord k i · D_{Y_i} f`, where `D_Y` is the
  operator of the real Lie direction `Y` (`realOperator`, module `EnergyBound`); the enveloping
  generator map is real linear and the enveloping action is complex linear.
- `energy_nonneg`: the energy `∑_i re b(D_{Y_i} e, D_{Y_i} e)` is nonnegative.
- `sum_bandNorm_basisDerivative_le_of b hb e`: for any unitary form `b` with
  `bandNorm S f = re b(f, f)` for all `f`,
  `∑_k bandNorm(D_k e) ≤ (∑_k ∑_i cartanCoord k i²) · energy b e`
  (Cauchy–Schwarz for each `k`, then summation).
- `sum_bandNorm_basisDerivative_le`: the same for the band unitary form.
