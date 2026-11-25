# Analytic lemmas for the convergence of real Rankin–Selberg integrals

Helper module for the convergence part of the real local Rankin–Selberg theory (towards
`Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement`).
It imports only Mathlib. Every declaration is proved, and the module
uses no axioms beyond Lean's standard ones (`propext`, `Classical.choice`, `Quot.sound`).

All declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal.RealConvergenceAnalysis`. The module has three
independent parts. Together they turn the gauge estimate of the module `RealWhittakerGauge`
and the Iwasawa integration formula of the module `RealIwasawaMeasure` into absolute
convergence and holomorphy of the zeta integrals.

Provenance. In Jacquet, *Archimedean Rankin–Selberg integrals* (2009), the Whittaker gauge
estimate is Proposition 3.1 (pp. 15–16, proved from derivatives along simple roots), and the
equal-rank convergence majorant is Lemma 3.5, integral (3.10) (p. 14), applied in §5.1
(p. 32). The estimates of this module are not taken from those proofs. The exponent
inequality in logarithmic torus coordinates, the integrability of `exp(−c ∑ |x_j|)`, and the
holomorphy argument by differentiation under the integral sign were devised for this
formalization. They play the role of Lemma 3.5 and of the continuity statement (5.1) in
§5.1.

## Holomorphy of exponential families of integrals

- `abs_mul_exp_le`: for `δ > 0` and `|t − t₀| ≤ δ`,
  `|ℓ| · exp(t ℓ) ≤ (exp((t₀ + 2δ) ℓ) + exp((t₀ − 2δ) ℓ)) / δ`.
  Proof: `δ|ℓ| ≤ exp(δ|ℓ|)`, and `exp(tℓ + δ|ℓ|)` is bounded by one of the two exponentials,
  according to the sign of `ℓ`.
- `norm_cexp_mul_ofReal`: `‖exp(s x)‖ = exp(Re(s) · x)` for `s ∈ ℂ` and real `x`.
- `differentiableOn_integral_cexp_mul`: let `μ` be a measure on `X`, let `f : X → ℂ` and
  `ℓ : X → ℝ` be almost everywhere strongly measurable, and suppose that
  `‖f‖ · exp(t ℓ)` is integrable for every real `t > σ`. Then
  `s ↦ ∫ f(x) · exp(s · ℓ(x)) dμ(x)` is complex differentiable (holomorphic) on the
  half-plane `{s : σ < Re s}`.
  Proof: at `s₀` put `δ = (Re s₀ − σ)/3`. On the ball of radius `δ` about `s₀`, the
  `s`-derivative `f · ℓ · exp(sℓ)` of the integrand is dominated, by `abs_mul_exp_le`, by
  `(‖f‖ exp((Re s₀ + 2δ)ℓ) + ‖f‖ exp((Re s₀ − 2δ)ℓ))/δ`. This bound is integrable because
  both exponents exceed `σ`. Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
  then gives differentiability under the integral sign.

## Integrability of `exp(−c ∑ |x_j|)`

- `integrable_exp_neg_mul_abs`: for `c > 0`, `x ↦ exp(−c|x|)` is Lebesgue integrable on `ℝ`.
  It is glued from Mathlib's integrability on `(0, ∞)` and on `(−∞, 0]`.
- `integrable_exp_neg_mul_sum_abs`: for `c > 0`, `x ↦ exp(−c ∑_j |x_j|)` is integrable on
  `ℝ^n` (`Fin n → ℝ` with the product Lebesgue measure). It is a product of one-variable
  integrable functions (`Integrable.fintype_prod`).
- `lintegral_exp_neg_mul_sum_abs_lt_top`: the same statement as a finite lower Lebesgue
  integral of `ENNReal.ofReal (exp(−c ∑_j |x_j|))`.

## Simple-root coordinates and the exponent inequality

For `y ∈ ℝ^(r+1)` (indexed by `Fin (r+1)`), the simple-root coordinates are
`y_i − y_(i+1)` for `i < r`.

- `rootPos y = ∑_(i<r) max(y_i − y_(i+1), 0)`, the sum of their positive parts. This is the
  quantity in which the gauge estimate `RealWhittakerGauge.exists_gauge_bound` gives
  arbitrarily fast exponential decay. `rootPos (−y)` is the sum of their negative parts, and
  `rootPos_nonneg` states that both are nonnegative.
- `sum_root_eq`: `∑_(i<r) (y_i − y_(i+1)) = rootPos y − rootPos (−y)`.
- `sub_last_le_partial`, `sub_last_le`: `y_j − y_r ≤ rootPos y` for every `j` (telescoping
  from `j` to `r` and dropping negative terms; the partial version is the induction
  statement, by reverse induction on `j`).
- `last_sub_le`: `y_r − y_j ≤ rootPos (−y)`.
- `sum_sub_last_le`: `∑_j (y_j − y_r) ≤ (r+1) · rootPos y − rootPos (−y)`. Write
  `y_i − y_r = (y_i − y_(i+1)) + (y_(i+1) − y_r)` for `i < r`, sum the first terms with
  `sum_root_eq`, and bound the second ones by `sub_last_le`.
- `sum_abs_le`: `∑_j |y_j| ≤ (r+1) · (|y_r| + rootPos y + rootPos (−y))`.
- `exponent_le` (**exponent inequality**): let `n = r + 1`, `A ≥ 0`, `(A+1) n ≤ t`, and let
  `M` and `K` both be at least `(A+1) n + t n`. Then

  `−M · rootPos y + A ∑_j |y_j| + t ∑_j y_j − K · max(y_r, 0) ≤ −∑_j |y_j|`.

  In the application `t` is the real part of `s` (the integrand carries `|det g|^s` and
  `log|det g| = ∑_j y_j` on the torus). `M` is the gauge decay exponent. `K` is the decay of
  the Schwartz function `Φ` evaluated on the last row of `g`, which has size `exp(y_r)`.
  `A` collects the fixed growth exponents of the two Whittaker functions and the modular
  character of the Iwasawa measure.
  Proof: write `∑_j y_j = n y_r + ∑_j (y_j − y_r)`, use `sum_sub_last_le` and `sum_abs_le`,
  and treat the cases `y_r ≥ 0` and `y_r ≤ 0` separately. In the second case the
  determinant term `t n y_r ≤ (A+1) n y_r` absorbs the growth `(A+1) n |y_r|`. The coefficient
  of `rootPos (−y)` is `(A+1) n − t ≤ 0`, so the negative root parts need no decay from the
  Whittaker functions.
