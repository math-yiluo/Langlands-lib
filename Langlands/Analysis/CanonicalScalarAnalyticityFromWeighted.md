# Canonical scalar regularity from the weighted factorial estimate

This helper module of `Langlands.Analysis.ScalarEllipticAnalyticityProof`
connects the weighted factorial derivative estimate for elliptic solutions to
canonical Euclidean analytic regularity. Here the estimate is an explicit
premise, and the module proves no estimate. The final module instantiates the
premise with the published theorem `canonicalScalarWeightedFactorialBounds`.

## `canonicalEuclideanScalarEllipticAnalyticity_of_weightedFactorialBounds`

For `d r : ℕ` with `0 < d` and `0 < r`, the theorem shows that
`CanonicalScalarWeightedFactorialBoundsStatement d r` implies
`CanonicalEuclideanScalarEllipticAnalyticityStatement d r`.

Take an operator `D` on `EuclideanSpace ℝ (Fin d)` whose basis is the canonical
basis. Take an open set `S`, analytic coefficients and ellipticity on `S`, and
a complex function `F` with `ContDiffOn ℝ ∞ F S` and `D.action F x = 0` on `S`.
`AnalyticOnNhd ℝ F S` means analyticity at each point, so fix `x₀ ∈ S`.

1. Apply the weighted estimate at `x₀` with upper radius `R₀ = 1`. It gives a
   radius `0 < R` with `closedBall x₀ R ⊆ S`, constants `C` and `A`, and for
   every `k : ℕ` the bound
   `ballWeightedSeminorm (derivWordNorm k F) x₀ R k ≤ ofReal (C * A ^ k * k!)`.
   The bound `R ≤ 1` and the positivity of `C` and `A` are not used.
2. Smoothness of `F` restricts from `S` to the open ball `ball x₀ R`, since
   `ball x₀ R ⊆ closedBall x₀ R ⊆ S`.
3. `ballWeightedSeminorm` and `derivWordNorm` (from the published module
   `Langlands.Analysis.LocalEllipticCutoffEstimate`) unfold definitionally to
   the explicit premise of the published `weightedL2FactorialAnalyticity d`.
   That premise is the supremum over `ρ ∈ [R/2, R)` of
   `ofReal ((R - ρ)^k)` times the `L²` norm on `ball x₀ ρ` of the square root
   of the sum, over all ordered canonical basis words of length `k`, of the
   squared norms of `iteratedFDeriv ℝ k F`. So that theorem applies directly
   and gives `AnalyticAt ℝ F x₀`.

## `canonicalEuclideanScalarEllipticAnalyticity_of_all_weightedFactorialBounds`

Assuming `CanonicalScalarWeightedFactorialBoundsStatement d r` for all
`d r : ℕ`, this theorem proves the canonical assertion for every `d r : ℕ`,
including zero. It applies `canonicalEuclideanScalarEllipticAnalyticity_of_positive`
from `Langlands.Analysis.EuclideanScalarEllipticAnalyticityDegenerate` to the
previous theorem. The zero cases need no weighted estimate.

Neither theorem changes the operator, its full equation with every lower-order
term, its canonical basis, analytic coefficients or ellipticity hypotheses.

## Imports and provenance

The module imports the published statement
`Langlands.Analysis.CanonicalScalarWeightedFactorialBoundsStatement`, the
published proof module `Langlands.Analysis.WeightedL2FactorialAnalyticity` and
the helper `Langlands.Analysis.EuclideanScalarEllipticAnalyticityDegenerate`.
Step 3 is the Lean form of a step in Morrey–Nirenberg (1957, §5, printed
p. 288 / PDF p. 18). Right after (5.5), they state that analyticity follows
from Lemma 2.3 and its corollary, printed pp. 276–277 / PDF pp. 6–7. The
supremum over `ρ ∈ [R/2, R)` of radius-weighted `L²` norms matches their
normalized seminorm (5.4) for a scalar equation, before division by the
factorial. The choice of radius, the composition and the zero-case reduction
are internal.

Worker 116 wrote the Lean code in a shared draft for this task, and Worker 1130
rewrote this explanation for submission.
