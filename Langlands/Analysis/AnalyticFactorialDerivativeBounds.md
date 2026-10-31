# Uniform factorial bounds for the derivatives of real-analytic functions

Module `Langlands.Analysis.AnalyticFactorialDerivativeBounds`, namespace
`Langlands.Analysis`. It imports Mathlib and the Library module
`Langlands.Analysis.CoordinateScalarDifferentialOperator`, which provides
`CoordinateScalarOperator` and `CoordinateScalarOperator.AnalyticCoefficientsOn`.

## Conventions

`E` is a real normed space (`NormedAddCommGroup E`, `NormedSpace ℝ E`). It may
be infinite-dimensional and need not be complete. `F` is a real normed space.
The analytic results assume `F` complete (`CompleteSpace F`); the coefficients
of a coordinate scalar operator take values in `ℂ`, which is complete.
`D^j f(y)` means Mathlib's `iteratedFDeriv ℝ j f y`, a continuous
`j`-multilinear map, and `‖D^j f(y)‖` is its operator norm. Balls are open
balls `Metric.ball x₀ R`. Analyticity is real analyticity: `AnalyticAt ℝ` and
`AnalyticOnNhd ℝ`.

## Definition

- `HasFactorialDerivativeBoundsOn f s C A` (for `f : E → F`, `s : Set E`,
  `C A : ℝ`) means: for every `y ∈ s` and every order `j : ℕ`,
  `‖D^j f(y)‖ ≤ C * A ^ j * j!`.

The definition only names this family of inequalities. It does not assert
smoothness, which is why the analytic results below record analyticity on
the ball separately. The constants come before `y` and `j`, so a single pair
`(C, A)` works for all points of `s` and all orders. At order `j = 0` the
inequality reads `‖f y‖ ≤ C`.

## Results

### Elementary properties

- `HasFactorialDerivativeBoundsOn.norm_iteratedFDeriv_le`: the defining
  inequality at a point of `s`.
- `HasFactorialDerivativeBoundsOn.norm_iteratedFDeriv_apply_le`: the bound
  applied to vectors, `‖D^j f(y) v‖ ≤ C * A ^ j * j! * ∏ i, ‖v i‖` for
  `v : Fin j → E`. When every `v i` has norm `1` (for instance a word of
  vectors of the standard basis of `EuclideanSpace ℝ (Fin d)`) the product is
  `1`; this special case is not stated separately in the module.
- `HasFactorialDerivativeBoundsOn.mono`: the bounds restrict to subsets.
- `HasFactorialDerivativeBoundsOn.mono_const`: the bounds persist when `C` and
  `A` are enlarged, provided `0 ≤ A`.

### Power series facts

- `norm_iteratedFDeriv_le_of_hasFPowerSeriesOnBall`: if `f` has the power
  series `p` on a ball centred at `x` and `F` is complete, then
  `‖D^j f(x)‖ ≤ j! * ‖p j‖`. This follows from Mathlib's
  `HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace`, which writes
  `D^j f(x) v` as the sum of `p j (v ∘ σ)` over the `j!` permutations `σ`.
- `norm_changeOriginSeries_apply_le`: for every formal multilinear series
  `p`, all `k, l : ℕ` and `x : E`, the `k`-multilinear map
  `p.changeOriginSeries k l (fun _ => x)` has operator norm at most
  `2 ^ (k + l) * ‖p (k + l)‖ * ‖x‖ ^ l`. The multilinear map
  `p.changeOriginSeries k l` is a sum of `(k + l).choose l` terms, each of
  norm `‖p (k + l)‖` (Mathlib's
  `FormalMultilinearSeries.norm_changeOriginSeriesTerm`), and
  `(k + l).choose l ≤ 2 ^ (k + l)`; evaluating at the constant vector
  `fun _ => x` of length `l` contributes the factor `‖x‖ ^ l`.
- `norm_changeOrigin_le`: let `r : ℝ≥0` with `r > 0` and `C : ℝ` satisfy
  `‖p n‖ * r ^ n ≤ C` for all `n`, and let `‖x‖ ≤ r / 4`. Then
  `‖p.changeOrigin x k‖ ≤ 2 * C * (2 / r) ^ k` for every `k`. Here
  `p.changeOrigin x k` is Mathlib's sum over `l` of the terms
  `p.changeOriginSeries k l (fun _ => x)`. The term bound above gives at most
  `C * (2 / r) ^ k * (1 / 2) ^ l` for the `l`-th term, and the geometric
  series sums to `2`. This lemma and the previous one do not assume `F`
  complete.

### Factorial bounds from analyticity

- `exists_ball_hasFactorialDerivativeBoundsOn_of_analyticAt`: if `F` is
  complete and `f` is real analytic at `x₀`, then there are `R > 0`, `C > 0`
  and `A > 0` with `HasFactorialDerivativeBoundsOn f (Metric.ball x₀ R) C A`.
- `exists_ball_le_hasFactorialDerivativeBoundsOn_of_analyticAt`: for every
  prescribed `R₀ > 0` the radius can be taken with `R ≤ R₀`, and `f` is
  moreover analytic at every point of the ball (`AnalyticOnNhd ℝ`). In
  particular `f` is `ContDiffOn ℝ n` on that ball for every smoothness level
  `n`, by Mathlib's `AnalyticOnNhd.contDiffOn_of_completeSpace`; that
  consequence is not restated in this module.
- `CoordinateScalarOperator.AnalyticCoefficientsOn.exists_ball_hasFactorialDerivativeBoundsOn`:
  let `D : CoordinateScalarOperator E d r` satisfy `D.AnalyticCoefficientsOn S`,
  let `x₀ ∈ S` and `R₀ > 0`. Then there are `R` with `0 < R ≤ R₀`, and
  `C > 0`, `A > 0`, such that for every order `k : Fin (r + 1)` and every word
  `w : Fin k.val → Fin d` the coefficient `D.coefficient k w` is analytic at
  every point of `Metric.ball x₀ R` and satisfies
  `HasFactorialDerivativeBoundsOn (D.coefficient k w) (Metric.ball x₀ R) C A`.
  One ball and one pair of constants serve all the finitely many
  coefficients. The set `S` need not be open; analyticity at `x₀` alone
  already gives analyticity on a small ball.

## Proof outline

Let `f` have the power series `p` on the ball of radius `r` around `x₀`.
Choose `0 < ρ < r` in `ℝ≥0`. Since `ρ` is below the radius of convergence,
Mathlib's `FormalMultilinearSeries.norm_mul_pow_le_of_lt_radius` gives `C > 0`
with `‖p n‖ * ρ ^ n ≤ C` for all `n`. Take the ball of radius `ρ / 4` and the
constants `2 * C` and `2 / ρ`. For `y` in that ball, put `z = y - x₀`. Mathlib's
`HasFPowerSeriesOnBall.changeOrigin` shows that `f` has the power series
`p.changeOrigin z` on a ball centred at `x₀ + z = y`. Hence
`‖D^j f(y)‖ ≤ j! * ‖p.changeOrigin z j‖ ≤ j! * 2 * C * (2 / ρ) ^ j`.

For the `R ≤ R₀` variant, the set of points where `f` is analytic is open
(Mathlib's `AnalyticAt.eventually_analyticAt`). Shrink the ball to the minimum
of the bound radius, a radius on which `f` is analytic, and `R₀`.

For the operator coefficients, the pairs `(k, w)` form a finite type. Apply the
variant to each coefficient. A finite intersection of neighbourhoods of `x₀` is
a neighbourhood (`Filter.eventually_all`), so it contains a ball; cap its
radius by `R₀`. The common constants are `1 + ∑ C_(k,w)` and `1 + ∑ A_(k,w)`.
They dominate each individual constant, so `mono_const` gives the bounds.

## Provenance

The results are internal derived content. They are the classical Cauchy-type
estimates for the derivatives of a real-analytic function, uniform on a small
ball. They are proved here from Mathlib's power series API. No statement from
the literature is formalized verbatim. The module is intended to supply
analytic-coefficient bounds of the form `‖D^j a(y)‖ ≤ C * A ^ j * j!` to the
variable-coefficient factorial recursion in the scalar elliptic regularity
chain for task `d7081753-2858-442a-bd34-eda72b059529`; that use is not part
of this module.

The results carry no hypotheses beyond the ones listed above: `E` need not
be complete or finite-dimensional, `F` is assumed complete only where stated,
and the set `S` in the operator result need not be open.
