# Proof of holomorphy of positive-weight Mellin integrals

Author: Worker 740.

## Result

`Langlands.Analysis.mellinHalfPlane` proves the published closed proposition
`Langlands.Analysis.MellinHalfPlaneStatement` in every universe `u`; its type
is exactly `MellinHalfPlaneStatement.{u}`. The statement and its Markdown are
imported unchanged. No hypothesis is added: the measure is arbitrary (not
assumed finite or sigma-finite), `κ` is an arbitrary real number, and the
integral is Mathlib's Bochner integral of Mathlib's `Complex.cpow`.

The module imports, in addition to the statement module,
`Mathlib.Analysis.SpecialFunctions.Pow.Deriv` (derivative of `z ↦ a ^ z`) and
`Mathlib.MeasureTheory.Function.SpecialFunctions.Basic` (measurability of the
complex power and the complex logarithm).

## Elementary inequalities

Three private real-variable lemmas carry the estimates.

- `mul_abs_log_le_rpow_add_rpow_neg`: for `0 < r` and `0 < h`,
  `h * |log r| ≤ r ^ h + r ^ (-h)`. Apply `Real.log_le_sub_one_of_pos` to
  `r ^ h` and to `r ^ (-h)`, rewrite with `Real.log_rpow`, and conclude by
  `abs_le` because both powers are positive.
- `rpow_le_rpow_add_rpow`: for `0 < r` and `A ≤ y ≤ B`,
  `r ^ y ≤ r ^ A + r ^ B`. If `r ≤ 1` the power is antitone in the exponent,
  so `r ^ y ≤ r ^ A`; if `1 ≤ r` it is monotone, so `r ^ y ≤ r ^ B`. The other
  summand is nonnegative.
- `rpow_mul_abs_log_le`: for `0 < r`, `0 < h`, `A ≤ u - h` and `u + h ≤ B`,
  `r ^ u * |log r| ≤ 2 / h * (r ^ A + r ^ B)`. Indeed
  `h * (r ^ u * |log r|) ≤ r ^ u * (r ^ h + r ^ (-h)) = r ^ (u + h) + r ^ (u - h)`,
  and both exponents `u ± h` lie in `[A, B]`, so the previous lemma bounds each
  term by `r ^ A + r ^ B`. Dividing by `h` gives the claim.

## Main proof

Fix `X`, `μ`, `c`, `d`, `κ` and the four hypotheses.

1. *Measurability.* `AEMeasurable.complex_ofReal` turns `AEMeasurable d μ`
   into almost-everywhere measurability of `x ↦ (d x : ℂ)`. The instance
   `Complex.hasMeasurablePow` gives, through `AEMeasurable.pow_const`, the
   almost-everywhere measurability of `x ↦ (d x : ℂ) ^ w` for every `w : ℂ`,
   and `AEMeasurable.clog` that of `x ↦ Complex.log (d x : ℂ)`. Since `ℂ` is
   second countable these upgrade to `AEStronglyMeasurable`, and products with
   the given `AEStronglyMeasurable c μ` give the measurability of every
   integrand `c x * (d x : ℂ) ^ (s - κ)` and of every candidate derivative
   `c x * ((d x : ℂ) ^ (s - κ) * Complex.log (d x : ℂ))`.
2. *Norms.* By `Complex.norm_cpow_eq_rpow_re_of_pos` and `0 < d x`,
   `‖c x * (d x : ℂ) ^ (s - κ)‖ = ‖c x‖ * d x ^ (s.re - κ)` (real power).
   By `Complex.ofReal_log` and `Complex.norm_real`,
   `‖Complex.log (d x : ℂ)‖ = |Real.log (d x)|`.
3. *Local setup.* Let `s₀` satisfy `0 < s₀.re`, and choose `h = s₀.re / 4`, so
   `0 < h` and `2 * h < s₀.re`. The endpoint parameters `s₀.re - 2 * h` and
   `s₀.re + 2 * h` are positive reals.
4. *Integrability at the center.* By step 2 the integrand at `s₀` has the same
   pointwise norm as the integrand at the real parameter `s₀.re`, which is
   integrable by hypothesis; `Integrable.mono` with step 1 gives integrability
   at `s₀`.
5. *Pointwise derivative.* For each `x` and `s`, `HasDerivAt.const_cpow` (the
   base `(d x : ℂ)` is nonzero) composed with `s ↦ s - κ`, then multiplied by
   `c x`, shows that `s ↦ c x * (d x : ℂ) ^ (s - κ)` has derivative
   `c x * ((d x : ℂ) ^ (s - κ) * Complex.log (d x : ℂ))` at `s`.
6. *Domination.* For `s` in the open ball of radius `h` about `s₀`,
   `|s.re - s₀.re| ≤ ‖s - s₀‖ < h` by `Complex.abs_re_le_norm`. With step 2
   the derivative norm is `‖c x‖ * (d x ^ (s.re - κ) * |Real.log (d x)|)`.
   Applying `rpow_mul_abs_log_le` with `u = s.re - κ`,
   `A = s₀.re - 2 * h - κ` and `B = s₀.re + 2 * h - κ` bounds it, for every
   `x`, by
   `2 / h * (‖c x * (d x : ℂ) ^ ((s₀.re - 2 * h) - κ)‖ + ‖c x * (d x : ℂ) ^ ((s₀.re + 2 * h) - κ)‖)`,
   with both parameters cast from reals. This bound is integrable: it is a
   constant multiple of the sum of the norms of the hypothesis integrands at
   the two positive real endpoints.
7. *Conclusion.* `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the
   neighborhood `Metric.ball s₀ h` and steps 1, 4, 5 and 6 gives `HasDerivAt`
   of `s ↦ ∫ x, c x * (d x : ℂ) ^ (s - κ) ∂μ` at `s₀`. Hence the function is
   differentiable at `s₀`, and so within the half-plane at `s₀`. As `s₀` was an
   arbitrary point of `{s : ℂ | 0 < s.re}`, this is the stated
   `DifferentiableOn`.

The integrability of the integrand at points other than `s₀`, and of the
derivative, is not needed separately: the dominated differentiation theorem
only requires integrability at the center and an integrable bound for the
derivative on the neighborhood.

## Scope and provenance

This is the internal analytic lemma stated by
`Langlands.Analysis.MellinHalfPlaneStatement`; the proof follows the route
proposed in the statement's Markdown, with the constant `2 / h` instead of
`h⁻¹` in the derivative bound because the estimate of step 6 sums two
endpoint powers for each of the two shifted exponents. It uses only pinned
Mathlib results and no external literature. It supplies no Whittaker
integrability, continuation beyond the half-plane, or derivative formula as
a separate declaration.
