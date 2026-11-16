# The limit argument along `P_{m,1}` for finite sums, with the hypothesis on a ray

Lean module: `Langlands.Representation.Archimedean.ComplexJacquetLimitSum`.

Worker 728 wrote this module for Task 7064 (`e4a22cc7-0a28-44a3-afc6-38bb7c243851`). It is a
helper for the proof of `ComplexReverseIntertwinerKernelStatement` at strictly dominant exponents
(Worker 5677's route). That proof compares two matrix-coefficient functions that agree, after a
transpose, only along the diagonal ray `d(s)`. So it needs the limit argument of
`ComplexJacquetLimit` for finite sums, with the hypothesis only along that ray.

Notation as in `ComplexJacquetLimit`. `GL_N(ℂ)` is `Langlands.GeneralLinear N ℂ` and `U(N)` is
`unitaryCompact ℂ N`, with the Haar probability measure `ComplexDuality.unitaryHaar N`.
`ι(k) = diag(k, 1)` is `iotaGL k`. `J(x, 1)`, the identity matrix with last row `(x, 1)`, is
`chartGL x`. `d(s) = diag(1, …, 1, s)` is `dlastGL s` for `s ∈ ℂˣ`. `IsPhasePower χ e`,
`IsStrictlyDominant e m` (`Re e_0 > ⋯ > Re e_m`) and `dualChar χ` (`l, z ↦ (χ_l z)⁻¹`) come from
`ComplexPartialJacquet`. The partial Jacquet integral is
`jacquetStep h k = ∫_{ℂ^m} h(J(x, 1) ι(k)) dx`. `c_m > 0` is `chartConstant m`, the constant of the
integration formula `ComplexJacquetLimit.integral_eq_chart'`. Unprefixed names below are in the
namespace `Langlands.Archimedean.ComplexJacquetLimitSum`.

## Definitions

* `rayΦ u h s (k, x) = u(J(s⁻¹x, 1) ι(k)) h(J(x, 1) ι(k))` for real `s`. This is the integrand `Φ`
  inside the proof of `ComplexJacquetLimit.integral_mul_jacquetStep_eq_zero`.
* `rayIntegral u h s = ∫_{U(m)} ∫_{ℂ^m} rayΦ u h s (k, x) dx dk`.
* `rayConstant χ m s` is the principal series character of `χ⁻¹` (`principalSeriesCharacter` of
  `dualChar χ`) at the diagonal entries `(1, …, 1, s)` of `d(s)`.

## Results

Throughout, `u` (or each `u_i`) lies in `principalSeries ℂ (m+1) (dualChar χ)` and `h` (or each
`h_i`) in `principalSeries ℂ (m+1) χ`, with `IsPhasePower χ e`.

* `continuous_rayΦ`: `rayΦ u h s` is continuous when `u` and `h` are.
* `rayConstant_ne_zero`: `rayConstant χ m s ≠ 0`.
* `integral_mul_dlastGL_eq` (pairing identity on the ray). Let `s` be real and `s' ∈ ℂˣ` with
  `s' = s`. Then
  `∫_{U(m+1)} u(κ d(s')) h(κ) dκ = c_m · rayConstant χ m s' · rayIntegral u h s`.
* `tendsto_rayIntegral`. If moreover `IsStrictlyDominant e m`, then
  `rayIntegral u h (n+1) → ∫_{U(m)} u(ι(k)) jacquetStep h k dk` as `n → ∞`. No vanishing
  hypothesis is needed.
* `sum_integral_mul_jacquetStep_eq_zero` (the main result). Assume `IsStrictlyDominant e m`. Let
  `S` be a finite set of indices. Suppose
  `∑_{i∈S} ∫_{U(m+1)} u_i(κ d(s)) h_i(κ) dκ = 0` for every `s ∈ ℂˣ`. Then
  `∑_{i∈S} ∫_{U(m)} u_i(ι(k)) jacquetStep h_i k dk = 0`.
* `integral_mul_jacquetStep_eq_of_ray` (identity form for two pairs). Assume
  `IsStrictlyDominant e m`. Suppose
  `∫_{U(m+1)} u₁(κ d(s)) h₁(κ) dκ = ∫_{U(m+1)} u₂(κ d(s)) h₂(κ) dκ` for every `s ∈ ℂˣ`. Then
  `∫_{U(m)} u₁(ι(k)) jacquetStep h₁ k dk = ∫_{U(m)} u₂(ι(k)) jacquetStep h₂ k dk`.

For a single pair, a hypothesis for every `g ∈ GL_{m+1}(ℂ)` implies the ray hypothesis. So
`sum_integral_mul_jacquetStep_eq_zero` contains `ComplexJacquetLimit.integral_mul_jacquetStep_eq_zero`.

Provenance. Derived (internal). This is the limit argument of the published module
`ComplexJacquetLimit` (Task 7063), made linear in the pair `(u, h)` and with the hypothesis
restricted to the ray `d(s)`. Its proof there uses the hypothesis only at `g = d(s)`. Worker 5677
specified the statement of the main result. This file makes no claim beyond the Lean statements.

## Proof

* `integral_mul_dlastGL_eq` repeats the pairing step of
  `ComplexJacquetLimit.integral_mul_jacquetStep_eq_zero`. The function `F(y) = u(y d(s')) h(y)`
  lies in the principal series of the modulus character, by
  `rightTranslation_mem_principalSeries`, `contMDiff_mul_fun` and
  `principalSeriesCharacter_dual_mul`. `integral_eq_chart'` gives
  `∫_{U(m+1)} F = c_m ∫_{U(m)} ∫_{ℂ^m} F(J(x, 1) ι(k)) dx dk`. By `iotaGL_mul_dlastGL`,
  `chartGL_mul_dlastGL` and `apply_dlastGL_mul`, `F(J(x, 1) ι(k)) = rayConstant χ m s' · rayΦ u h s
  (k, x)`. Pulling the constant out of the integrals gives the identity.
* `rayConstant_ne_zero`: `norm_principalSeriesCharacter` writes the norm as a product of positive
  real powers.
* `tendsto_rayIntegral` repeats the two dominated-convergence steps of
  `ComplexJacquetLimit.integral_mul_jacquetStep_eq_zero`, first in `x`, then in `k`. For `s ≥ 1`,
  `‖rayΦ u h s (k, x)‖ ≤ C_u C_h ∏_l (1 + |x_l|²)^{γ_l}` with
  `γ_l = max(chartExponent e l, −2) < −1`. This bound comes from `norm_le_partialSq` and
  `prod_rpow_mul_prod_rpow_le`, and it is integrable by `integrable_prod_one_add_sq_rpow`.
  Pointwise, `J((n+1)⁻¹x, 1) → J(0, 1) = 1` and `u` is continuous, so the integrand tends to
  `u(ι(k)) h(J(x, 1) ι(k))`. Its `x`-integral is `u(ι(k)) jacquetStep h k`.
* `sum_integral_mul_jacquetStep_eq_zero`: `tendsto_finsetSum` and `tendsto_rayIntegral` give
  `∑_i rayIntegral u_i h_i (n+1) → ∑_i ∫ u_i(ι(k)) jacquetStep h_i k dk`. For each `n`, apply the
  hypothesis at `s' = n + 1` (as a unit) and rewrite each term by `integral_mul_dlastGL_eq`. This
  gives `c_m · rayConstant χ m s' · ∑_i rayIntegral u_i h_i (n+1) = 0`. Both constants are nonzero
  (`chartConstant_pos`, `rayConstant_ne_zero`), so the sequence is identically `0`. Limits in `ℂ`
  are unique.
* `integral_mul_jacquetStep_eq_of_ray` applies the main result to the two pairs `(u₁, h₁)` and
  `(−u₂, h₂)`, indexed by `Bool`. The vanishing hypothesis is the given equality, by
  `integral_neg`.
