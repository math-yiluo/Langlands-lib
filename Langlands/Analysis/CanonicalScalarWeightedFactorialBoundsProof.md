# Actual weighted factorial derivative bounds

Worker 94 wrote the Lean proof. Worker 881 rewrote its companion documentation.

## Result

`Langlands.Analysis.canonicalScalarWeightedFactorialBounds` proves
`CanonicalScalarWeightedFactorialBoundsStatement d r` for all natural numbers
`d` and `r` (implicit binders `{d r : ℕ}`). The published statement is
unchanged. It concerns the actual `CoordinateScalarOperator` `D` on
`EuclideanSpace ℝ (Fin d)` with the canonical basis. The coefficients of
`D` are real analytic on an open set `S`, and its principal symbol is
elliptic at every point of `S`. The function `u` is a complex
`ContDiffOn ℝ ∞` function on `S` with `D.action u = 0` on `S`; this equation
includes every lower-order term. For every `x₀ ∈ S` and `R₀ > 0` the theorem
gives `0 < R ≤ R₀` with `closedBall x₀ R ⊆ S` and constants `C, A > 0`. These
satisfy, for every `k`, including `k = 0`,

`ballWeightedSeminorm (derivWordNorm k u) x₀ R k ≤ ENNReal.ofReal (C * A ^ k * k!)`.

The premises `0 < d` and `0 < r` are part of the statement. The proof uses
`0 < r` (for local ellipticity and the discrete induction) and never uses
`0 < d`. When `d = 0` or `r = 0` the statement is vacuous, and the theorem
proves nothing further about those cases. The theorem does not prove real
analyticity of `u` and does not transport the result to other norms or
coordinates.

## Published results used

The module imports the following Library modules by Lean name.

- `Langlands.Analysis.CanonicalScalarWeightedFactorialBoundsStatement`, the
  target statement. Through it the module also gets
  `Langlands.Analysis.LocalEllipticCutoffEstimate`, which provides
  `derivWordNorm`, `constCoeffAction`, `ballWeightedSeminorm`,
  `ConstCoeffL2Bound`, `continuousOn_derivWordNorm`,
  `derivWordNorm_congr_of_eventuallyEq`, `constCoeffL2Bound_of_statement` and
  the cutoff recursion `exists_factorial_weighted_recursion`.
- `Langlands.Analysis.CoordinateScalarFrozenDerivativeEstimateProof`, the
  published proof `coordinateScalarFrozenDerivativeEstimate` of
  `CoordinateScalarFrozenDerivativeEstimateStatement`. It bounds the
  ordered derivative tensor of the frozen principal action pointwise. The
  bound is the derivative of the full action, plus the principal coefficient
  variation times the order `p+r` solution tensor, plus Leibniz sums with
  exact binomial factors.
- `Langlands.Analysis.AnalyticFactorialDerivativeBounds`, which provides
  `HasFactorialDerivativeBoundsOn` (`‖D^j f y‖ ≤ C A^j j!`) and
  `CoordinateScalarOperator.AnalyticCoefficientsOn.exists_ball_hasFactorialDerivativeBoundsOn`.
  The latter gives one ball of radius at most `R₀` and common positive
  constants for all coefficients of `D`.
- `Langlands.Analysis.CoordinateScalarLocalEllipticityProof`, which provides
  `coordinateScalarLocalEllipticity`.
- `Langlands.Analysis.ConstantCoefficientEllipticL2EstimateProof`, which provides
  `constantCoefficientEllipticL2Estimate`.

The proof also uses `orderedDerivativeFamilyNorm_eq_sqrt`
(`Langlands.Analysis.OrderedDerivativeFamilyNorm`) and
`contDiffOn_infty_iteratedLineDeriv`
(`Langlands.Analysis.SmoothIteratedFDerivSymm`), both imported by the
frozen-action modules.

## Proof outline

The module's private helpers come in the order below.

**Coefficient tensors.** `singletonTensorNorm_le_card_pow` compares the
singleton ordered derivative tensor norm with `card(I)^j` times the operator
norm of the order-`j` derivative. It holds for any finite family of directions
of norm at most one in a real normed space. The proof bounds the finite
Euclidean norm by the sum of the word norms, then bounds each word by the
operator norm. With the canonical basis this gives
`derivWordNorm j f x ≤ d^j ‖D^j f(x)‖`, including order zero. Combined with
`HasFactorialDerivativeBoundsOn f s C A`, it gives
`derivWordNorm j f x ≤ C (d A)^j j!` on `s`. This loss of `d^j` is applied
only to coefficient derivatives of order `j`. It is never applied to the
solution tensors of total order `p+r`.

**Finiteness.** A real function that is continuous on a closed ball of
nonnegative radius `R` has finite weighted seminorm for every weight exponent
`m`. Compactness bounds the function, and the ball has finite volume. Every
weight `(R-ρ)^m` with `R/2 ≤ ρ < R` is at most `R^m`, and each smaller open
ball has a smaller `L²` norm. Together with `continuousOn_derivWordNorm`, this
shows the seminorm of every derivative order is finite whenever `u` is smooth
on an open set containing the closed ball.

**Seminorm calculus.** The helpers prove the following properties of
`ballWeightedSeminorm`:

- monotonicity under a pointwise bound on the outer open ball, for a
  function continuous on that ball;
- the triangle inequality and the finite-sum inequality;
- the bound for multiplication by a nonnegative real constant;
- the change of weight exponent from `n` to `m ≥ n`, at cost `R^(m-n)`.

**Frozen pointwise estimate.** `canonicalFrozen_pointwise_le` specializes
`coordinateScalarFrozenDerivativeEstimate` to the canonical basis. Since
`D.action u = 0` on an open set, germ locality
(`derivWordNorm_congr_of_eventuallyEq`) makes every derivative of the full
action vanish there. The coefficient tensors are bounded uniformly by `b(j)`,
and the summed principal-coefficient variation
`∑_w ‖a_w(x₀) - a_w(x)‖` is at most `ε`. Under these bounds the order-`p`
tensor of the frozen action `L⁰u = constCoeffAction (a(x₀)) u` is at most
the sum of three parts:

- `ε` times the order-`p+r` solution tensor;
- a principal Leibniz sum with factors `choose(p, j+1) b(j+1)`;
- a lower-order Leibniz sum with factors `choose(p, j) b(j)`, for
  coefficients of order `k < r`.

**Weighted frozen estimate.** `canonicalFrozen_weighted_le` lifts the
pointwise estimate to the seminorm with weight exponent `p+r`, using
monotonicity, then the triangle and finite-sum inequalities. Each solution term
gets its own weight. The principal coefficient derivative of order `j+1` costs
`R^(j+1)`. A lower coefficient of order `k`, differentiated `j` times, costs
`R^(r-k+j)`. Monotonicity needs continuity of the frozen action's
derivative norm. This holds because the frozen action is a finite sum of
constant multiples of iterated line derivatives, so it is smooth on open sets.
Every order `p`, including `p = 0`, is covered.

**Passage to real numbers.** `canonicalFrozen_real_le` proves that every
product and finite sum in the weighted estimate is finite, then applies
`toReal`. Every coefficient and radius power is nonnegative, so
`toReal (ofReal c) = c`.

**Factorial normalization.** Set `N(m)` to the real value of
`ballWeightedSeminorm (derivWordNorm m u) x₀ R m` and
`H(m) = N(m) / (m-r)!`, with truncated subtraction. The helper
`choose_factorial_cancel` gives `choose(p, j) j! / p! = 1/(p-j)!`. For lower
coefficients, `lower_factorial_cancel_le` bounds the remaining inverse
factorial by the one at the truncated index `p-j+k-r`. Take coefficient
bounds `b(j) = C L^j j!` and count the `d^r` (respectively `d^k`) ordered
words at each coefficient order. `normalized_frozen_bound` then shows that
`M(p)/p!` is at most

`ε H(r+p) + C d^r ∑_{j<p} (LR)^(j+1) H(p-(j+1)+r)
 + ∑_{k<r} C d^k R^(r-k) ∑_{j≤p} (LR)^j H(p-j+k)`.

Here `M(p)` is the real seminorm of the order-`p` frozen-action tensor with
weight exponent `r+p`. No bound on `R` is imposed.

**Cutoff recursion.** `exists_factorial_weighted_real_recursion` turns the
published `exists_factorial_weighted_recursion` into the real inequality

`H(r+p) ≤ K₃ (M(p)/p! + ∑_{q=1}^r H(r+p-q))`

for all `p ≥ 0`. The conversion first proves that all products and the finite
sum are finite. It also uses `(r+p-q) - r = p - q`, which holds even under
truncated subtraction. The constant `K₃` depends only on the frozen
coefficients and the `L²` constant `K`. It is chosen before the center,
radius and function.

**Discrete majorant.** This part does not involve the PDE.

- `geometric_convolution_le`: if `t, A ≥ 0` and `2t ≤ A`, then
  `∑_{j=0}^n t^j A^(n-j) ≤ 2 A^n`, because each term is at most
  `A^n (1/2)^j`.
- `sequence_convolution_le` extends this to convolutions against a sequence
  already bounded by `C A^m`.
- `exponential_bound_of_elliptic_recurrence` takes `r > 0` and a nonnegative
  real sequence with

  `H(r+p) ≤ B [T ∑_{j<p} t^(j+1) H(p-(j+1)+r)
   + ∑_{k<r} S(k) ∑_{j≤p} t^j H(p-j+k) + ∑_{q=1}^r H(r+p-q)]`,

  where `B, T, t, S(k)` are nonnegative. It proves `H(m) ≤ C A^m` for all
  `m`, with `Q = 2Tt + 2∑_k S(k) + r`, `A = 1 + 2t + BQ` and
  `C = 1 + ∑_{m<r} H(m)`. The strong induction handles `m < r` by the
  finite base bound `C`. For `m ≥ r`, every recurrence index is strictly
  smaller than `m`, even with truncated subtraction. The three sums then
  contribute at most `Q C A^(m-1)`, so `BQ ≤ A` closes the induction.

**Absorption.** `absorb_half` turns `x ≤ K(x/(2K) + Y)` into `x ≤ 2KY`.
`exponential_bound_of_frozen_recursion` combines the cutoff recursion with the
normalized frozen bound for `ε = 1/(2K₃)`. This gives the discrete recurrence
with `B = 2K₃`, `T = C d^r`, `t = LR` and `S(k) = C d^k R^(r-k)`. Then
`factorial_bound_of_normalized_exponential_bound` gives
`N(m) ≤ C₀ A₀^m (m-r)! ≤ C₀ A₀^m m!`.

**Fixed ball.** `exists_radius_independent_weighted_factorial_bound` fixes the
frozen coefficients and `K` and chooses `K₃` first. Take any radius
`R ≥ 0` with `closedBall x₀ R ⊆ S` and the frozen `ConstCoeffL2Bound` on
`ball x₀ R`. Assume coefficient bounds `C L^j j!` on the ball and variation at
most `1/(2K₃)`. Then the all-order bound holds in `ℝ≥0∞`. Finiteness of the
solution and frozen-action seminorms comes from smoothness on the open set
`S ⊇ closedBall x₀ R`. That finiteness is also what allows the final return
from real numbers to `ℝ≥0∞`.

**Choice of the ball.** The main theorem proceeds in these steps.

1. Continuity of the principal coefficients at `x₀` and ellipticity at `x₀`
   go into `coordinateScalarLocalEllipticity`. This gives an open
   neighborhood of `x₀` and `c > 0` with
   `c ‖ξ‖^r ≤ |principal symbol at x|` there for all real covectors `ξ`;
   only the point `x = x₀` is used.
2. Evaluating at the covector `innerSL ℝ ξ` turns this into the frequency
   lower bound for the frozen coefficients. That covector has norm `‖ξ‖`,
   and its values on the canonical basis are the coordinates of `ξ`.
   `constCoeffL2Bound_of_statement constantCoefficientEllipticL2Estimate`
   then gives `ConstCoeffL2Bound (a(x₀)) c⁻¹` on every set.
3. `K₃` is chosen for `K = c⁻¹`.
4. The analytic coefficient bound gives one ball `ball x₀ R₁`, with
   `R₁ ≤ R₀`, and common constants `C, A`. The tensor comparison above
   replaces `A` by `d A`.
5. The summed principal variation is continuous at `x₀` and equals zero
   there, so it is below `1/(2K₃)` on some `ball x₀ δ ⊆ S`.
6. With `R = min(R₁, δ)/2` we have `closedBall x₀ R ⊆ ball x₀ δ ⊆ S` and
   `R < R₁ ≤ R₀`. The fixed-ball result now gives the stated bound.

## Relation to Morrey–Nirenberg (1957), §5

The source is C. B. Morrey and L. Nirenberg, *On the analyticity of the
solutions of linear elliptic systems of partial differential equations*,
Comm. Pure Appl. Math. 10 (1957), 271–290. Page numbers below are printed
pages. The
project's route is recorded in the Library note
`notes/automorphic/elliptic-analyticity-source-map.md`.

**Dictionary.** For one scalar equation of order `r` (`N = 1`, so
`s + t = r` in (1.4)–(1.6), p. 273), the quantities in (5.3) are as follows
(p. 287):

- `d_p(u, B_ρ)` is the `L²` norm of `|∇^(r+p) u|` on `B_ρ`;
- `e_p(f, B_ρ)` is the `L²` norm of `|∇^p f|`;
- the tensor norm `|∇^m u|` of §2 is `derivWordNorm m u`.

The definitions (5.4) (p. 288) use the convention `[p!] = 1` for `p < 0`
from (3.12) (p. 281). With them, the Lean sequence satisfies exactly

`H(m) = N(m)/(m-r)! = N_{R, m-r}(u)` for every `m ≥ 0`.

Truncated subtraction gives `(m-r)! = 1 = [(m-r)!]` when `m < r`. The balls
are centered at `x₀` rather than at the origin. MN write the equation as
`L⁰u = f + (L⁰ - L)u = F`, where `L⁰` has the principal coefficients frozen at
the center (p. 289). Here `f = 0`, `F = L⁰u`, and `M(p)/p! = M_{R,p}(F)`.

**Steps that follow the source.**

- The published `exists_factorial_weighted_recursion` is the scalar form of
  Lemma 5.3, (5.9).
- The absorbed recurrence above corresponds to Lemma 5.4 (p. 290). Lemma 5.4
  reads `N_{R,p} ≤ 2K₃{L(AR)^p Z₃ R^(s+t+ν/2) + 2L ∑_{τ=1}^{p+s+t} (AR)^τ
  N_{R,p-τ} + ∑_{q=1}^{s+t} N_{R,p-q}}`.
  - The factor `2K₃` is the same. In the Lean proof it comes from absorbing
    the principal variation term into the left side.
  - The `Z₃` term, which comes from `f`, is absent because `f = 0`.
  - A principal term of index `j+1` is MN's `τ = j+1`.
  - A lower-order coefficient of order `k` contributes `N_{R,p-τ}` with
    `τ = j + r - k`, which lies in `1, …, p+r`. Its weight is
    `R^(r-k) (LR)^j` instead of `(AR)^τ`.
- MN then obtain (5.5), `N_{R,p}(u) ≤ M λ^p`, "by induction on p from
  Lemma 5.4", following Theorem 1 with `λ` from (4.8) (p. 285). The bound
  `H(m) ≤ C A^m` is (5.5) with `M = C A^r` and `λ = A`.

**Internal adaptations.** These steps are not taken from the source.

- Only the scalar equation is treated, with an arbitrary center.
- MN make the variation small with the Lipschitz bound in (5.10) and the
  radius `R₁` of (5.11). Here the variation is made smaller than `1/(2K₃)`
  by continuity of the coefficients at `x₀`.
- MN state Lemma 5.4 without proof and say they "omit the proofs which are
  very similar" (p. 287). Here its analogue is derived from the published
  frozen-action Leibniz estimate.
- The coefficient bounds come from operator-norm factorial bounds. The
  word-norm conversion changes `A` to `d A`.
- In place of `λ = 6 + 6K₃ + 3AR₁` from (4.8), the induction uses the
  explicit majorant `Q`, `A = 1 + 2t + 2K₃Q` and `C = 1 + ∑_{m<r} H(m)`.
- The base cases are only `m < r` (MN's `p < 0`). This works because the
  cutoff recursion also holds at `p = 0`.
- The constants depend on the chosen radius, while MN's `λ` is uniform for
  `R < R₁`. The ball itself is chosen as `R = min(R₁, δ)/2`.
- The proof includes the finiteness and `toReal` conversions, and the final
  estimate `(m-r)! ≤ m!`.

The article attributes no automorphic conclusion to this estimate, and this
module claims none.
