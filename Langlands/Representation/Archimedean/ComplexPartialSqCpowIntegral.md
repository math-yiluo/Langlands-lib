# Integrals of complex powers of partial square sums

Lean module: `Langlands.Representation.Archimedean.ComplexPartialSqCpowIntegral`, namespace
`Langlands.Archimedean.ComplexPartialSqCpow`.

This module holds no statement definition. It computes the integrals needed for the Jacquet
integral of spherical vectors (`ComplexSphericalJacquet`). All content is internal. Complex
powers are Mathlib's `Complex.cpow` of positive real numbers.

Notation: `r_l(x) = 1 + ∑_{j<l} |x_j|²` for `x ∈ ℂ^m` (Library
`ComplexParabolicChartBound.partialSq`).

## One complex variable

- `add_one_ne_zero_of_re`, `ne_neg_one_of_re`: `Re β < -1` implies `β + 1 ≠ 0` and `β ≠ -1`.
- `hasDerivAt_add_sq_cpow`: for `A > 0` and `Re β < -1`, `r ↦ (A + r²)^{β+1}/(β+1)/2` has
  derivative `r (A + r²)^β` (Mathlib `hasDerivAt_ofReal_cpow_const'` composed with
  `r ↦ A + r²`).
- `norm_add_sq_cpow`: `|(A + r²)^β| = (A + r²)^{Re β}`; `tendsto_add_sq_cpow`: for `Re γ < 0`,
  `(A + r²)^γ → 0` as `r → ∞`.
- `integral_Ioi_mul_add_sq_cpow`: `∫_0^∞ r (A + r²)^β dr = -A^{β+1}/(β+1)/2`. This is the
  fundamental theorem of calculus on `(0, ∞)` (`integral_Ioi_of_hasDerivAt_of_tendsto`).
  Integrability holds because the norm `r (A + r²)^{Re β}` is the nonnegative derivative of a
  real function with a limit at infinity (`integrableOn_Ioi_deriv_of_nonneg`).
- `integral_add_sq_cpow`: `∫_ℂ (A + |t|²)^β dt = -π A^{β+1}/(β+1)`. Proof in polar coordinates
  (`Complex.integral_comp_polarCoord_symm`). On `polarCoord.target = (0, ∞) × (-π, π)` the
  integrand is `r (A + r²)^β · 1`. `setIntegral_prod_mul` splits it into the radial integral and
  `∫_{-π}^{π} 1 = 2π`.

## Several variables

- `integrand m β δ y = r_m(y)^δ ∏_{l<m} r_{l+1}(y)^{β_l}` for `β : Fin m → ℂ`, `δ ∈ ℂ`.
- `continuous_partialSq_cpow`, `norm_partialSq_cpow`, `continuous_integrand`.
- `integrable_integrand`: for `Re β_l < -1` and `Re δ ≤ 0` the integrand is integrable. Its
  norm is the real integrand with exponents `Re β_l`, `Re δ`, which is integrable by the
  Library's `ComplexPartialSqIntegral.integrable_partialSq_mul_prod` (the tail condition holds
  because every tail sum contains a negative term `Re β_j + 1` and the other terms are negative).
- `integral_integrand_ne_zero`: for `Re β_l < -1` and `Re δ ≤ 0`,
  `∫_{ℂ^m} r_m(y)^δ ∏_{l<m} r_{l+1}(y)^{β_l} dy ≠ 0`. Induction on `m`, following the Library's
  proof of `integrable_partialSq_mul_prod`:
  - `m = 0`: the integrand is `1` on a one-point space of measure `1`.
  - `m + 1`: split `ℂ^{m+1} = ℂ × ℂ^m` with the last coordinate first
    (`MeasurableEquiv.piFinSuccAbove`, measure preserving).
  - Since `r_{l+1}(y, t) = r_{l+1}(y)` for `l < m` and `r_{m+1}(y, t) = r_m(y) + |t|²`, the
    integrand is `(r_m(y) + |t|²)^{β'} · integrand m γ 0 y` with `β' = δ + β_m` and
    `γ_l = β_l` for `l < m`.
  - Fubini (`integral_prod_symm`) and `integral_add_sq_cpow` turn the `t`-integral into
    `-π/(β'+1) · r_m(y)^{β'+1}`. So the integral equals
    `-π/(β'+1) · ∫ integrand m γ (β'+1)`.
  - `Re(β' + 1) < Re δ ≤ 0`, so the induction hypothesis applies, and `π/(β'+1) ≠ 0`.

## Provenance

Internal. The value `∫_ℂ (A + |t|²)^β dt = -π A^{β+1}/(β+1)` is an elementary computation. The
iterated integral is the rank-one factorization of the Harish-Chandra `c`-function along the
maximal parabolic subgroups `P_{m,1}` (Gindikin–Karpelevich). Only its nonvanishing is stated
here, and no literature statement is used.
