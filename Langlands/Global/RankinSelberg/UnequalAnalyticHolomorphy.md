# Holomorphy of integrals with exponential moments

Provenance: internal. This module is a generic supporting lemma module for the proof of
`Langlands.Global.RankinSelbergGlobal.UnequalAnalyticStatement` (Cogdell 2004, Theorem 2.1).
Cogdell deduces that the unequal-rank global integral is entire and bounded in vertical
strips from its absolute convergence for every `s`. The Lean proof writes the integral as
`∫ A(x) exp (s L(x)) dμ(x)` with `L = log |det|` and applies the three statements of this
module. Nothing here is specific to automorphic forms.

Setting: `μ` is a measure on a measurable space `X`, `A : X → ℂ`, `L : X → ℝ`, and the
standing hypothesis `hint` says that `x ↦ ‖A x‖ · exp (σ L x)` is integrable for every real
`σ`. All declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal.UnequalAnalytic`.

## Declarations

- `exp_mul_le_add L ha hb`: for `a ≤ σ ≤ b`, `exp (σ L) ≤ exp (a L) + exp (b L)`. Proof:
  split on the sign of `L`; the exponential is monotone, so `exp (σ L)` is at most
  `exp (b L)` when `L ≥ 0` and at most `exp (a L)` when `L ≤ 0`.
- `abs_le_exp_add_exp_neg L`: `|L| ≤ exp L + exp (-L)`, from `x + 1 ≤ exp x` applied to
  `L` and `-L`.
- `abs_mul_exp_le L h`: if `|σ - a| ≤ 1` then
  `|L| exp (σ L) ≤ exp ((a+2) L) + 2 exp (a L) + exp ((a-2) L)`. Proof: bound `|L|` by the
  previous lemma and `exp (σ L)` by `exp ((a-1) L) + exp ((a+1) L)`, multiply out.
- `norm_mul_cexp A s L`: `‖A · exp (s L)‖ = ‖A‖ · exp (re s · L)`.
- `aestronglyMeasurable_mul_cexp`: `x ↦ A x · exp (s L x)` is a.e. strongly measurable when
  `A` and `L` are.
- `integrable_mul_cexp` (**absolute convergence**): under `hint`, for every complex `s` the
  function `x ↦ A x · exp (s L x)` is integrable. Proof: its norm equals
  `‖A x‖ exp (re s · L x)`, which is integrable by `hint (re s)`.
- `differentiable_integral_mul_cexp` (**holomorphy**): under `hint`, the function
  `s ↦ ∫ A x · exp (s L x) dμ` is complex differentiable on all of `ℂ`. Proof: at `s₀`,
  differentiate under the integral sign (Mathlib
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`) on the unit ball around `s₀`. The
  `s`-derivative of the integrand is `A x · exp (s L x) · L x`; for `s` in the ball,
  `|re s - re s₀| ≤ 1`, so by `abs_mul_exp_le` its norm is at most
  `‖A x‖ (exp ((re s₀ + 2) L x) + 2 exp (re s₀ · L x) + exp ((re s₀ - 2) L x))`, which is
  integrable by `hint` at the three parameters.
- `exists_norm_integral_mul_cexp_le` (**boundedness in vertical strips**): under `hint`,
  for real `a, b` there is `C ≥ 0` with `‖∫ A x · exp (s L x) dμ‖ ≤ C` whenever
  `a ≤ re s ≤ b`. Proof: take
  `C = ∫ (‖A x‖ exp (a L x) + ‖A x‖ exp (b L x)) dμ` and bound the norm of the integrand
  pointwise with `exp_mul_le_add`.
