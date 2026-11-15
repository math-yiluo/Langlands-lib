# Integrals over `U(n)` of functions of the last row

Lean module: `Langlands.Representation.Archimedean.ComplexLastRowIntegral`.

Worker 140 wrote this module for Task 7063 (`f2d2e257-dd4b-4820-96ab-faa9c832ffb8`), the proof of
`ComplexStandardLanglandsQuotientStatement`. It is the unitary counterpart of the Library module
`OrthogonalLastRowIntegral` (Worker 5220, for `O(n)`), with the same proof through a Gaussian.

The module computes the integral over `U(m+1)` of a function of the last row, for functions that
are homogeneous of degree zero under complex scalars. Such an integral is a weighted Lebesgue
integral over the affine chart `v ↦ (v, 1)` of `ℂ^m`. The statement is
`Langlands.Archimedean.ComplexLastRowIntegralStatement`, proved as
`Langlands.Archimedean.complexLastRowIntegral`. In the proof of
`ComplexStandardLanglandsQuotientStatement` it is the measure part of the integration formula for
the maximal parabolic subgroup `P_{m,1}` of `GL_{m+1}(ℂ)`: `P_{m,1} \ GL_{m+1}(ℂ)` is parametrized
by the last row up to complex scaling, and the chart `(v, 1)` corresponds to the opposite unipotent
radical `v ↦ [[1, 0], [v, 1]]`.

Notation: `U(m+1)` is the subgroup `unitaryCompact ℂ (m+1)` of `Langlands.GeneralLinear (m+1) ℂ`,
with the Library's Haar probability measure `ComplexDuality.unitaryHaar (m+1)` for its Borel
σ-algebra. Row vectors are `Fin (m+1) → ℂ` with Lebesgue measure `volume` (the product of the
Lebesgue measures on `ℂ ≅ ℝ²`). `Fin.snoc v 1` is the row vector `(v, 1)`. Declarations without a
prefix are in the namespace `Langlands.Archimedean.ComplexLastRowIntegral`.

## The statement

`ComplexLastRowIntegralStatement`: let `m` be a natural number and `Φ : (Fin (m+1) → ℂ) → ℂ` be

* measurable,
* bounded (`‖Φ x‖ ≤ C` for some `C`),
* homogeneous of degree zero under complex scalars: `Φ(s • x) = Φ(x)` for every complex `s ≠ 0`.

Then

`∫_{U(m+1)} Φ(k_{m,·}) dk = c_m · ∫_{ℂ^m} Φ(v, 1) · (1 + ∑ |vᵢ|²)^{-(m+1)} dv`,

where `k_{m,·}` is the last row of `k` and
`c_m = (∫_ℂ |t|^(2m) e^{-|t|²} dt) / (∫_{ℂ^{m+1}} e^{-∑ |xᵢ|²} dx)`. In Lean both constants are
written as integrals.

Provenance. Derived, internal infrastructure. That the last row of a Haar-random unitary matrix is
uniformly distributed on the unit sphere of `ℂ^(m+1)`, and the form of that measure in the chart
`v ↦ (v,1)/|(v,1)|` of complex projective space, are standard. The proof here does not use surface
measure on the sphere; it goes through a Gaussian on `ℂ^(m+1)`.

## Definitions

* `sqNorm x = ∑ |xᵢ|²` (`ofReal_sqNorm`: as a complex number it is `x ⬝ᵥ star x`),
  `gaussian x = exp(-sqNorm x)`.
* `lastRow k`: the last row of `k ∈ U(m+1)`.
* `IsHomogeneousZero Φ`: `Φ(s • x) = Φ(x)` for complex `s ≠ 0`.
* `gaussianMoment m = ∫_ℂ |t|^(2m) e^{-|t|²} dt` and `chartWeight v = ((1 + sqNorm v)^(m+1))⁻¹`.

## Proof

1. **Linear changes of variables** (`integral_comp_linearEquiv`). For a `ℂ`-linear automorphism
   `L` of `ℂ^k`, `∫ g(L x) dx = |det L|⁻² ∫ g(x) dx`: the real determinant of `L` is the norm
   `|det L|²` of its complex determinant (Mathlib's `LinearMap.det_restrictScalars` with
   `Algebra.norm_complex_apply`), and `Measure.map_linearMap_addHaar_eq_smul_addHaar` applies.
   In particular right multiplication `x ↦ x κ` by a unitary `κ` preserves Lebesgue measure
   (`integral_vecMul`, `|det κ| = 1`) and `sqNorm` (`sqNorm_vecMul`), and complex scaling
   `v ↦ s • v` of `ℂ^m` multiplies it by `|s|^(2m)` (`integral_comp_complex_smul`).
2. **Householder** (`exists_unitary_lastRow`). Every unit row vector `u` is the last row of a
   unitary matrix. Choose `θ` with `|θ| = 1` and `conj(θ) u_m` real and nonnegative
   (`sqNorm_eq_one_lastRow_phase`). The vector `u' = conj(θ) u` is the last row of `1` if `u' = e_m`,
   and otherwise of the Hermitian reflection `1 − (2/|w|²) w* w` with `w = e_m − u'`
   (`exists_unitary_lastRow_of_real`; `|w|² = 2(1 − u'_m)` is real). Then
   `diag(1, …, 1, θ)` times that reflection is unitary with last row `u`.
3. **Transitivity** (`integral_vecMul_eq`). For `x ≠ 0`, `∫_{U(m+1)} Φ(x k) dk = ∫ Φ(lastRow k) dk`.
   Write `x = r · lastRow k₀` with `r = |x|` and `k₀` from step 2; use homogeneity,
   `lastRow (k₀ k) = lastRow k₀ · k` (`lastRow_mul`) and left invariance of Haar measure.
4. **Averaging** (`integral_mul_gaussian_eq`).
   `∫ Φ(x) e^{-|x|²} dx = (∫ Φ(lastRow k) dk) · ∫ e^{-|x|²} dx`. Average step 1 over `k`
   (`unitaryHaar` is a probability measure), exchange the integrals by Fubini
   (`integral_integral_swap`; the integrand is bounded by `C e^{-|x|²}`, integrable as a product of
   one-variable Gaussians on `ℂ`, `integrable_gaussian`), and apply step 3 for `x ≠ 0`; `{0}` is a
   null set.
5. **Chart** (`integral_mul_gaussian_chart`).
   `∫ Φ(x) e^{-|x|²} dx = gaussianMoment m · ∫ Φ(v,1) chartWeight(v) dv`. Split `x = (y, s)` with the
   last coordinate `s ∈ ℂ` (`volume_preserving_piFinSuccAbove`) and use Fubini (`integral_prod`).
   For `s ≠ 0` substitute `y = s v` (Jacobian `|s|^(2m)`, step 1). Homogeneity gives
   `Φ(s v, s) = Φ(v, 1)` (`snoc_smul_one`), so the integrand becomes
   `|s|^(2m) e^{-(1+|v|²)|s|²} Φ(v,1)`. Exchanging the integrals once more (integrability by
   `integrable_prod_iff'`, `integrable_norm_pow_mul_exp`, and `integrable_chartWeight`, which
   compares with Mathlib's `integrable_rpow_neg_one_add_norm_sq` in real dimension `2m`), the real
   scaling `t = √a s` of `ℂ` gives
   `∫_ℂ |s|^(2m) e^{-a|s|²} ds = a^{-(m+1)} ∫_ℂ |t|^(2m) e^{-|t|²} dt`
   (`integral_norm_pow_mul_exp_scale`, via `Measure.integral_comp_smul` with `finrank ℝ ℂ = 2`).
   Integrability of `|t|^(2m) e^{-a|t|²}` follows from `x^m ≤ m! e^x` and the integrability of
   Gaussians on `ℂ` (`GaussianFourier.integrable_cexp_neg_mul_sq_norm_add`).
6. **Conclusion** (`integral_lastRow`). Compare steps 4 and 5, and divide by
   `∫ e^{-|x|²} dx > 0` (`integral_gaussian_pos`).
