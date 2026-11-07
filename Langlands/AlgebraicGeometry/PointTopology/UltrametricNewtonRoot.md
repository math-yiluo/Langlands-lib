# Roots near approximate roots over ultrametric fields

Author: Worker 105; edited by Worker 1516.

This module proves a Newton-type root lemma over ultrametric valued fields, first over
complete fields and then, without completeness, over henselian valued fields. It is a
helper for the total disconnectedness of rational points of separated algebraic spaces
(Proposition 5.4 of Brian Conrad, *Weil and Grothendieck approaches to adelic points*,
December 31, 2011, printed p.15; source `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`). The route is
the author's; Conrad gives no argument for this part. Every lemma is proved in Lean.

## Complete ultrametric fields (`UltrametricNewton`)

Let `L` be a nontrivially normed field with ultrametric norm.

- `norm_eval_le`, `norm_eval_le_linear`, `norm_eval_sub_eval_le`, `norm_pow_sub_pow_le`:
  estimates for polynomials whose coefficients are bounded by `M`. A polynomial without
  terms of degree below two is bounded by `M ‖h‖²` on the unit ball and is
  `M ρ`-Lipschitz on the ball of radius `ρ ≤ 1`. A polynomial without constant term is
  bounded by `M ‖h‖`. These use `‖x^k - y^k‖ ≤ ‖x - y‖ ρ^(k-1)` and the ultrametric bound
  for finite sums.
- `exists_root`: if `L` is complete, `‖Q(t₀)‖ ≤ ‖Q'(t₀)‖`,
  `M ‖Q(t₀)‖ < ‖Q'(t₀)‖²`, and `M` bounds the Taylor coefficients `(taylor t₀ Q).coeff k`
  for `k ≥ 2`, then `Q` has a root `τ` with `‖τ - t₀‖ ≤ ‖Q(t₀)‖ / ‖Q'(t₀)‖` and
  `Q'(τ) ≠ 0`. Write `Q(t₀ + h) = c₀ + c₁ h + T(h)`, where `T` has no terms of degree below
  two. The map `h ↦ -(c₀ + T(h)) / c₁` sends the closed ball of radius
  `r = ‖c₀‖ / ‖c₁‖` into itself. It is a contraction with constant `M r / ‖c₁‖ < 1`. Its
  fixed point (Mathlib's `ContractingWith.fixedPoint`, on the complete closed ball) is a
  root. The derivative there is `c₁ + T'(h)` with `‖T'(h)‖ ≤ M r < ‖c₁‖`, so it is
  nonzero.

## Henselian fields

The completion `K̂` of an ultrametric normed field is ultrametric by the Library instance
`Langlands.Analytic.completion_isUltrametricDist` (`Langlands/Analysis/UltrametricCompletion.lean`).

- `exists_eq_of_simple_root_completion`: over a henselian valued field `K`
  (`IsHenselianValuedField K`), a simple root in the completion `K̂` of a polynomial with
  coefficients in `K` lies in `K`. The minimal polynomial of the root divides the given
  polynomial and has the root as a simple root. It is therefore irreducible with nonzero
  derivative, hence separable. The Library's `separableClosure_completion_eq_bot`
  (`HenselianEtalePointProof.lean`) says that `K` is separably closed in `K̂`.
- `exists_root_of_isHenselianValuedField`: over a henselian ultrametric field `K`, without
  completeness, the hypotheses of `exists_root` give a root `τ ∈ K` of `Q` with
  `‖τ - t₀‖ ≤ ‖Q(t₀)‖ / ‖Q'(t₀)‖`. (Unlike `exists_root`, the statement does not record
  `Q'(τ) ≠ 0`.) Apply `exists_root` in `K̂`, using the Library's
  `completionNontriviallyNormedField`. Then bring the simple root back to `K` by the
  previous lemma.
