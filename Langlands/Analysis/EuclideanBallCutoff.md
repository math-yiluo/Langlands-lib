# Smooth ball cutoffs with explicit derivative bounds

Module `Langlands.Analysis.EuclideanBallCutoff`, namespace
`Langlands.Analysis`.

## Conventions

`E` is a real inner product space (`NormedAddCommGroup` with
`InnerProductSpace ℝ E`). It may be infinite-dimensional, except in the two
compact-support results, which also assume `ProperSpace E`. The definitions
`ballCutoffProfile` and `ballCutoff` use only the norm, so their Lean
signatures assume only `NormedAddCommGroup E`. Several results also need only
the normed group structure of `E`. Their Lean statements drop the inner product
hypothesis with `omit [InnerProductSpace ℝ E] in`. The smoothness and
derivative bounds keep it, because they use the smoothness of `y ↦ ‖y‖^2`.
`F` is a real normed space (`NormedAddCommGroup` with `NormedSpace ℝ F`).

"Smooth" means `ContDiff ℝ ∞` or `ContDiffOn ℝ ∞`, with `open scoped ContDiff`.
Here `∞` is the `C^∞` level of `ℕ∞ω`, not the analytic level `ω`. `D^k f(x)`
means Mathlib's `iteratedFDeriv ℝ k f x`, a continuous `k`-multilinear map, and
`‖D^k f(x)‖` is its operator norm. `ball` and `closedBall` are `Metric.ball`
and `Metric.closedBall`. `Real.smoothTransition` is Mathlib's smooth function
`ℝ → ℝ`. It is `0` on `(-∞, 0]` and `1` on `[1, ∞)`, and its values lie in
`[0, 1]`.

Throughout, `R' = (ρ + R) / 2` denotes the middle radius. Most theorems about
the profile and the cutoff assume `0 ≤ ρ < R`; the exceptions are listed
below. The definitions accept arbitrary reals.

## Definitions

- `smoothTransitionDerivSup i` is the real supremum
  `⨆ t : ℝ, ‖D^i smoothTransition(t)‖`. The family is bounded above
  (`bddAbove_range_norm_iteratedFDeriv_smoothTransition`), so this is a genuine
  least upper bound.
- `ballCutoffConst k = k! · 4^k · ∑_{i=0}^{k} smoothTransitionDerivSup i`. It
  depends on `k` only, and not on `E`, `x₀`, `ρ` or `R`.
- `ballCutoffProfile ρ R y = (R'^2 - ρ^2)⁻¹ · (R'^2 - ‖y‖^2)`, the quadratic
  profile, for `y : E`.
- `ballCutoff x₀ ρ R x = smoothTransition (ballCutoffProfile ρ R (x - x₀))`, a
  function `E → ℝ`. `ballCutoff_apply` restates it as
  `smoothTransition ((R'^2 - ‖x - x₀‖^2) / (R'^2 - ρ^2))`.

The quadratic profile is used instead of `‖x - x₀‖` because it is smooth
everywhere, including at the centre.

## Results

### The transition function

- `iteratedFDeriv_smoothTransition_eq_zero`: for `i ≠ 0` and `t ∉ [0, 1]`,
  `D^i smoothTransition(t) = 0`. The function is locally constant there.
- `bddAbove_range_norm_iteratedFDeriv_smoothTransition`: for each `i`, the
  norms `‖D^i smoothTransition(t)‖`, `t : ℝ`, are bounded above. On `[0, 1]`
  this follows from continuity and compactness. Off `[0, 1]` the norm is at
  most `1` for `i = 0` and is `0` for `i ≥ 1`.
- `norm_iteratedFDeriv_smoothTransition_le`:
  `‖D^i smoothTransition(t)‖ ≤ smoothTransitionDerivSup i` for all `i` and `t`.
- `smoothTransitionDerivSup_nonneg` and `ballCutoffConst_nonneg`: both
  constants are `≥ 0`.

### The profile

- `contDiff_ballCutoffProfile`: the profile is `ContDiff ℝ n` for every
  `n : ℕ∞ω`, because it is a polynomial in `‖y‖^2`.
- `one_le_ballCutoffProfile`: if `0 ≤ ρ < R` and `‖y‖ ≤ ρ`, then the profile at
  `y` is `≥ 1`.
- `ballCutoffProfile_neg` and `ballCutoffProfile_nonpos`: if `0 ≤ ρ < R`, the
  profile is `< 0` when `R' < ‖y‖` and `≤ 0` when `R' ≤ ‖y‖`.
- `norm_iteratedFDeriv_ballCutoffProfile_le`: if `0 ≤ ρ < R`, `‖y‖ ≤ R'` and
  `1 ≤ i`, then `‖D^i (ballCutoffProfile ρ R)(y)‖ ≤ (4 / (R - ρ))^i`.

### The cutoff

All results in this subsection assume `0 ≤ ρ < R`, except `contDiff_ballCutoff`,
`ballCutoff_nonneg`, `ballCutoff_le_one` and `contDiff_ofReal_ballCutoff`, which
hold for all reals `ρ, R`.

- `contDiff_ballCutoff`: `ballCutoff x₀ ρ R` is `ContDiff ℝ ∞` on `E`.
- `ballCutoff_nonneg` and `ballCutoff_le_one`: its values lie in `[0, 1]`.
- `ballCutoff_eq_one`: it equals `1` on `closedBall x₀ ρ`.
- `ballCutoff_eq_zero`: it equals `0` at every point outside `ball x₀ R'`.
- `ballCutoff_eventuallyEq_one`: it equals `1` on a neighbourhood of every point
  of `ball x₀ ρ`.
- `ballCutoff_eventuallyEq_zero`: it equals `0` on a neighbourhood of every
  point outside `closedBall x₀ R'`.
- `support_ballCutoff_subset`: its support lies in `ball x₀ R'`.
- `tsupport_ballCutoff_subset_closedBall` and `tsupport_ballCutoff_subset_ball`:
  its closed support lies in `closedBall x₀ R'`, hence in `ball x₀ R`.
- `hasCompactSupport_ballCutoff` (assuming `ProperSpace E`): it has compact
  support.
- `norm_iteratedFDeriv_ballCutoff_le`: for every order `k : ℕ` and every
  `x : E`,

    `‖D^k (ballCutoff x₀ ρ R)(x)‖ ≤ ballCutoffConst k / (R - ρ)^k`.

  The bound holds for all `k` and all points, and the numerator depends only on
  `k`.
- `contDiff_ofReal_ballCutoff` and `norm_iteratedFDeriv_ofReal_ballCutoff_le`:
  the complex-valued cutoff `x ↦ (ballCutoff x₀ ρ R x : ℂ)` is
  `ContDiff ℝ ∞`. It satisfies the same bound
  `‖D^k‖ ≤ ballCutoffConst k / (R - ρ)^k`, with real derivatives.

### Products with the cutoff

Let `U : E → F`. All results in this subsection assume `0 ≤ ρ < R`.

- `contDiff_ballCutoff_smul`: if `U` is smooth on `ball x₀ R`
  (`ContDiffOn ℝ ∞ U (ball x₀ R)`), then `x ↦ ballCutoff x₀ ρ R x • U x` is
  smooth on all of `E`. Outside `closedBall x₀ R'` the product vanishes on a
  neighbourhood of each point, whatever `U` does there.
- `hasCompactSupport_ballCutoff_smul` (assuming `ProperSpace E`, any `U`): the
  product has compact support.
- `tsupport_ballCutoff_smul_subset` (any `U`): the closed support of the product
  lies in `closedBall x₀ R'`.
- `ballCutoff_smul_eventuallyEq` (any `U`): near every point of `ball x₀ ρ`, the
  product coincides with `U`.
- `norm_iteratedFDeriv_ballCutoff_smul_le`: if `U` is smooth on `ball x₀ R`,
  `x ∈ ball x₀ R` and `k : ℕ`, then

    `‖D^k (ballCutoff x₀ ρ R • U)(x)‖ ≤
      ∑_{i=0}^{k} C(k, i) · (ballCutoffConst i / (R - ρ)^i) · ‖D^(k-i) U(x)‖`.

## Proof outline

The profile is a constant multiple of `R'^2 - ‖y‖^2`. Its derivative is
`y ↦ -2 (R'^2 - ρ^2)⁻¹ ⟪y, ·⟫`, its second derivative is the constant bilinear
form `-2 (R'^2 - ρ^2)⁻¹ ⟪·, ·⟫`, and its derivatives of order `≥ 3` vanish. The
proof uses `R'^2 - ρ^2 = (R - ρ)(R + 3ρ)/4`, together with `‖y‖ ≤ R'` and
`ρ ≥ 0`. These give a bound of `4 / (R - ρ)` for the first derivative and
`(4 / (R - ρ))^2` for the second.

At points of `closedBall x₀ R'`, Mathlib's Faà di Bruno estimate
`norm_iteratedFDeriv_comp_le` gives `k! · C · D^k`. Here
`C = ∑_{i ≤ k} smoothTransitionDerivSup i` bounds the derivatives of
`smoothTransition` of every order `i ≤ k`, because each summand is
nonnegative. `D = 4 / (R - ρ)` bounds the profile's derivatives of orders
`1, …, k` in the form `D^i`. This product is
`ballCutoffConst k / (R - ρ)^k`. The translation by `x₀` is handled by
`iteratedFDeriv_comp_sub`. Outside `closedBall x₀ R'` the cutoff is locally `0`,
so its derivatives there are `0`. The complex-valued version composes with the
linear isometry `Complex.ofRealLI`.

The product results follow from the support statements. The Leibniz bound is
Mathlib's `norm_iteratedFDerivWithin_smul_le` on the open ball `ball x₀ R`. On
that ball, derivatives within the ball agree with ordinary derivatives.

## Provenance

Smooth cutoffs with derivative bounds of this kind are standard. The role of
this module comes from Morrey–Nirenberg 1957, "On the analyticity of the
solutions of linear elliptic systems of partial differential equations"
(registered source
`provided-17e51270c6d50eab8ff7b4142058b4ec69474b21e75225ec9952a95784e8229f`).
In the proof of Lemma 3.2 (printed page 281, PDF page 11) they take a fixed
function `h(τ)` of one variable of class `C^∞`, with `h(τ) = 1` for `τ ≤ 0` and
`h(τ) = 0` for `τ ≥ 1`. They set `ζ(x) = h((|x| - r)/δ)` and `v = ζ u`. So `ζ`
is `1` for `|x| ≤ r` and `0` for `|x| ≥ r + δ`. They then use that
"for `δ < r` we have `|∇^q ζ| ≤ Z_q δ^{-q}` with constants `Z_q` depending
only on `q`, `ν` and `h`", where `ν` is the dimension. In §5 (printed page 289,
PDF page 19) the interior Lemma 5.2 is derived "by the argument used to deduce
Lemma 3.2", and no separate cutoff is written there.

This module is a derived variant, proved independently. The fixed
one-variable function is Mathlib's `Real.smoothTransition`. It is composed with
a quadratic profile instead of `(|x| - r)/δ`. So the cutoff is smooth at the
centre, and no condition like `δ < r` is needed. The cutoff passes
from `1` on `closedBall x₀ ρ` to `0` outside `ball x₀ ((ρ + R) / 2)`. Its
derivative bound `ballCutoffConst k / (R - ρ)^k` has the shape
`Z_k δ^{-k}` with `δ = R - ρ`. The constant `ballCutoffConst k` is explicit.
Because it bounds operator norms of Fréchet derivatives on an arbitrary real
inner product space, it does not depend on the dimension, unlike `Z_q`. The
module proves no elliptic estimate. It only provides the cutoff, its derivative
bounds and the product rules for `ballCutoff x₀ ρ R • U`.
