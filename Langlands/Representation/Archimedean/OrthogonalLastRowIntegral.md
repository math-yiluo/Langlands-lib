# Integrals over `O(n)` of functions of the last row

Lean module: `Langlands.Representation.Archimedean.OrthogonalLastRowIntegral`.

This module computes the integral over `O(m+1)` of a function of the last row, for functions of
degree-zero homogeneity. Such an integral is a weighted Lebesgue integral over the affine chart
`v ↦ (v, 1)` of `ℝ^m`. The statement is `Langlands.Archimedean.OrthogonalLastRowIntegralStatement`,
proved as `Langlands.Archimedean.orthogonalLastRowIntegral`.

In the planned proof of `RealStandardLanglandsQuotientStatement` (Task 6749) this is the measure
part of the integration formula for the maximal parabolic subgroup `P_{m,1}` of `GL_{m+1}(ℝ)`.
`P_{m,1} \ GL_{m+1}(ℝ)` is parametrized by the last row up to scaling, and the chart `(v, 1)`
corresponds to the opposite unipotent radical `v ↦ [[1, 0], [v, 1]]`.

Notation: `O(m+1)` is the subgroup `unitaryCompact ℝ (m+1)` of `Langlands.GeneralLinear (m+1) ℝ`,
with the Library's normalized Haar measure `RealPrincipalSeriesDuality.haarK (m+1)` for its Borel
σ-algebra (`measurableSpaceK`). Row vectors are `Fin (m+1) → ℝ` with Lebesgue measure `volume`.
`Fin.snoc v 1` is the row vector `(v, 1)`. Declarations without a prefix are in the namespace
`Langlands.Archimedean.OrthogonalLastRowIntegral`.

## The statement

`OrthogonalLastRowIntegralStatement`: let `m` be a natural number and `Φ : (Fin (m+1) → ℝ) → ℂ` be

* measurable,
* bounded (`‖Φ x‖ ≤ C` for some `C`),
* homogeneous of degree zero: `Φ(s • x) = Φ(x)` for every real `s ≠ 0` (in particular `Φ` is even).

Then

`∫_{O(m+1)} Φ(k_{m,·}) dk = c_m · ∫_{ℝ^m} Φ(v, 1) · ((1 + ∑ vᵢ²)^{1/2})^{-(m+1)} dv`,

where `k_{m,·}` is the last row of `k` and
`c_m = (∫_ℝ |t|^m e^{-t²} dt) / (∫_{ℝ^{m+1}} e^{-∑ xᵢ²} dx)`. In Lean the weight is
`((Real.sqrt (1 + ∑ i, v i ^ 2)) ^ (m + 1))⁻¹` and both constants are written as integrals.

Provenance. Derived, internal infrastructure. The fact that the last row of a Haar-random
orthogonal matrix is uniformly distributed on the sphere is standard, as is the form of the
uniform measure in the gnomonic chart `v ↦ (v,1)/|(v,1)|`. The proof here does not use the
surface measure on the sphere. It goes through a Gaussian on `ℝ^{m+1}`.

## Definitions

* `sqNorm x = ∑ xᵢ²`, `gaussian x = exp(-sqNorm x)`.
* `lastRow k`: the last row of `k ∈ O(m+1)`.
* `IsHomogeneousZero Φ`: `Φ(s • x) = Φ(x)` for `s ≠ 0`.
* `gaussianMoment m = ∫ |t|^m e^{-t²} dt` and `chartWeight v = ((√(1 + sqNorm v))^{m+1})⁻¹`.

## Proof

1. **Rotation invariance** (`integral_vecMul`). Right multiplication `x ↦ x κ` by an orthogonal
   matrix `κ` preserves Lebesgue measure: it is a linear equivalence of determinant `±1`
   (`Measure.map_linearMap_addHaar_eq_smul_addHaar`). It also preserves `sqNorm`
   (`sqNorm_vecMul`).
2. **Householder** (`exists_orthogonal_lastRow`). Every unit row vector `u` is the last row of an
   orthogonal matrix. Take the identity if `u = e_m`, and otherwise the reflection
   `1 − (2/|w|²) w wᵀ` with `w = e_m − u`.
3. **Transitivity** (`integral_vecMul_eq`). For `x ≠ 0`, `∫_{O(m+1)} Φ(x k) dk = ∫ Φ(lastRow k) dk`.
   Write `x = r · lastRow k₀` with `r = |x|` and `k₀` from step 2. Use homogeneity and
   `lastRow (k₀ k) = lastRow k₀ · k` (`lastRow_mul`), then left invariance of Haar measure.
4. **Averaging** (`integral_mul_gaussian_eq`).
   `∫ Φ(x) e^{-|x|²} dx = (∫ Φ(lastRow k) dk) · ∫ e^{-|x|²} dx`. Average step 1 over `k`
   (`haarK` is a probability measure), exchange the integrals by Fubini (`integral_integral_swap`;
   the integrand is bounded by `C e^{-|x|²}`), and apply step 3 for `x ≠ 0`. `{0}` is a null set.
5. **Chart** (`integral_mul_gaussian_chart`).
   `∫ Φ(x) e^{-|x|²} dx = gaussianMoment m · ∫ Φ(v,1) chartWeight(v) dv`. Split `x = (y, s)` with the
   last coordinate `s` (`volume_preserving_piFinSuccAbove`), and use Fubini (`integral_prod`). For
   `s ≠ 0` substitute `y = s v` (`Measure.integral_comp_smul`, Jacobian `|s|^m`). Homogeneity gives
   `Φ(s v, s) = Φ(v, 1)` (`snoc_smul_one`), so the integrand becomes
   `|s|^m e^{-(1+|v|²)s²} Φ(v,1)`. Exchanging the integrals once more (integrability by
   `integrable_prod_iff'` and `integrable_chartWeight`, which compares with the Library lemma
   `integrable_rpow_neg_one_add_norm_sq`), the scaling `t = √a s` gives
   `∫ |s|^m e^{-a s²} ds = (√a)^{-(m+1)} ∫ |t|^m e^{-t²} dt` (`integral_abs_pow_mul_exp_scale`, via
   `Measure.integral_comp_mul_left`; integrability from `integrable_rpow_mul_exp_neg_mul_sq`).
6. **Conclusion** (`integral_lastRow`). Compare steps 4 and 5, and divide by
   `∫ e^{-|x|²} dx > 0` (`integral_gaussian_pos`).
