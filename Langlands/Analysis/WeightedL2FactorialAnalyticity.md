# Analyticity from weighted factorial L² derivative bounds

This module proves the published proposition
`Langlands.Analysis.WeightedL2FactorialAnalyticityStatement d` for every natural
dimension `d`, including zero. The domain is `EuclideanSpace ℝ (Fin d)` with
its standard volume, the values are complex, and the iterated derivatives and
analyticity are over the reals. The proof uses only the weighted factorial
bounds assumed in that proposition. It proves no estimate for solutions of a
differential equation and assumes no analytic regularity theorem.

## Notation

`euclideanBasisWordNorm T`, from the published module
`Langlands.Analysis.LocalSobolevPointwise`, is
`√(∑_{w : Fin k → Fin d} ‖T(e_{w 0}, …, e_{w (k-1)})‖²)`. Here `e` is
`EuclideanSpace.basisFun (Fin d) ℝ` and every ordered word `w`, including the
empty word when `k = 0`, is counted once. By definition (`euclideanBasisWordNorm_def`
is `rfl`) this is exactly the explicit square-root expression in the target
proposition, so the target's premise is accepted as written by the helper below.

## `fixedBall_factorial_bound_of_weighted`

Let `R > 0`, let `C, A` be arbitrary reals, and suppose that for every `k`

`sup_{ρ ∈ [R/2, R)} ofReal((R - ρ)^k) · ‖euclideanBasisWordNorm (D^k F)‖_{L²(ball x₀ ρ)} ≤ ofReal(C A^k k!)`,

where the supremum and L² seminorms are extended nonnegative reals. Then for
every `k`

`‖euclideanBasisWordNorm (D^k F)‖_{L²(ball x₀ (R/2))} ≤ ofReal(C (A/(R/2))^k k!)`.

No smoothness is needed for this step. The proof selects the term `ρ = R/2`,
which lies in `[R/2, R)` because `R > 0`; its weight is `ofReal((R/2)^k)`.
This weight is strictly positive and finite, so `ENNReal.mul_le_iff_le_inv`
moves it to the right-hand side as `ofReal(((R/2)^k)⁻¹)`. Since
`((R/2)^k)⁻¹ ≥ 0`, `ENNReal.ofReal_mul` combines the two factors into
`ofReal(((R/2)^k)⁻¹ · C A^k k!)`, and a ring identity rewrites the real number
as `C (A/(R/2))^k k!`. No sign condition on `C` or `A` is used.

## `weightedL2FactorialAnalyticity`

`weightedL2FactorialAnalyticity d : WeightedL2FactorialAnalyticityStatement d`.
Given `F`, `x₀`, `R > 0`, `C`, `A`, smoothness `ContDiffOn ℝ ∞ F (ball x₀ R)`
and the weighted bounds, the proof proceeds as follows.

1. Smoothness restricts to `ball x₀ (R/2)`.
2. `fixedBall_factorial_bound_of_weighted` gives the fixed-ball L² factorial
   bounds on `ball x₀ (R/2)`, with constants `C` and `A/(R/2)`.
3. The published
   `exists_norm_iteratedFDeriv_le_factorial_of_eLpNorm_euclideanBasisWordNorm_le`,
   applied on `ball x₀ (R/2)`, gives real constants `C'` and `M'` such that
   `‖D^k F(y)‖ ≤ C' M'^k k!` for every `k` and every `y ∈ ball x₀ (R/4)`
   (written `R / 2 / 2` in Lean). The norm is the operator norm of the
   iterated derivative.
4. Smoothness restricts further to `ball x₀ (R/2/2)`, and the published
   `analyticAt_of_iteratedFDeriv_le_factorial` from
   `Langlands.Analysis.FactorialDerivativeAnalyticity` gives `AnalyticAt ℝ F x₀`.

The target proposition, its Markdown and its imports are unchanged; this module
imports it together with the two published proof modules.

## Provenance

This proof is an internal assembly. The half-radius cancellation and the
assembly are by Worker 116, whose shared draft supplied the Lean unchanged.
The ordered basis-word convention and the two published results used in steps
3 and 4 are Worker 815's work: Worker 1085 submitted
`Langlands.Analysis.FactorialDerivativeAnalyticity` and Worker 347 submitted
`Langlands.Analysis.LocalSobolevPointwise`, both with Worker 815 as coauthor. The
radius-weighted convention is shared with Worker 94's scalar elliptic estimates.
Worker 1085 rewrote this Markdown to describe the Lean exactly.
