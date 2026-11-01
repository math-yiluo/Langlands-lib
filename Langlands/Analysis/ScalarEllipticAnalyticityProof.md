# Scalar analytic elliptic regularity

## Result

`Langlands.Analysis.scalarEllipticAnalyticity` proves the unchanged published
proposition `ScalarEllipticAnalyticityStatement E d r` (module
`Langlands.Analysis.ScalarEllipticAnalyticityStatement`). It holds for every
real normed space `E : Type v` in an arbitrary universe and for all
`d r : ℕ`, including `d = 0` and `r = 0`.

The proposition reads as follows. Let `D : CoordinateScalarOperator E d r` be
an actual scalar operator. It has a real basis of `E` indexed by `Fin d`,
complex coefficient functions for every order `k ≤ r` and every ordered word,
and the full action, including every lower-order term. Let `S` be an open set
and `F : E → ℂ` a function. Assume the following:

- the coefficients are real analytic on `S`;
- the real principal symbol is nonzero at every point of `S` on every
  nonzero real covector;
- `ContDiffOn ℝ ∞ F S`;
- `D.action F x = 0` for every `x ∈ S`.

Then `AnalyticOnNhd ℝ F S` holds, in the original norm and topology of `E`.
The theorem adds no hypothesis. In particular it assumes no uniform symbol
bound, no factorial derivative estimate, no positivity of `d` or `r` and no
canonical basis. A closing `example` restates the complete telescope
`∀ (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] (d r : ℕ), …` and
checks it against the theorem.

## Lean proof

The theorem is
`scalarEllipticAnalyticity_of_weightedFactorialBounds
(fun _ _ => canonicalScalarWeightedFactorialBounds) E d r`.
It supplies the published weighted estimate to the reduction in
`Langlands.Analysis.ScalarEllipticAnalyticityReduction`, so no estimate or
regularity assumption remains. Unfolding the three helper modules of this
contribution, the proof runs as follows.

1. **Positive dimension and order, canonical coordinates.**
   `canonicalEuclideanScalarEllipticAnalyticity_of_weightedFactorialBounds`
   (`CanonicalScalarAnalyticityFromWeighted`) fixes `x₀ ∈ S`. It applies the
   published `canonicalScalarWeightedFactorialBounds` with upper radius `1`.
   This gives `0 < R` with `closedBall x₀ R ⊆ S` and constants `C, A`
   such that, for every `k`, the supremum over `ρ ∈ [R/2, R)` of
   `(R - ρ)^k ‖D^k F‖_{L²(ball x₀ ρ)}` is at most `C A^k k!`. Here
   `‖D^k F‖` is the square root of the sum of the squared values of
   `iteratedFDeriv ℝ k F` on all ordered canonical basis words of length `k`.
   This bound is definitionally the premise of the published
   `weightedL2FactorialAnalyticity d`, which gives `AnalyticAt ℝ F x₀`.
   That theorem selects the term `ρ = R/2`. It then applies the published
   local Sobolev estimate on `ball x₀ (R/2)`, which gives pointwise factorial
   bounds on `ball x₀ (R/4)`, and the published factorial-derivative
   analyticity criterion.
2. **Zero cases.** `canonicalEuclideanScalarEllipticAnalyticity_of_positive`
   (`EuclideanScalarEllipticAnalyticityDegenerate`) handles `d = 0` and
   `r = 0` with the published `scalarEllipticAnalyticity_dimension_zero` and
   `scalarEllipticAnalyticity_order_zero`. Every remaining case has
   `0 < d` and `0 < r`. In dimension zero, `E` is a single point, so `F` is
   constant. At order zero, ellipticity makes the only coefficient nonzero,
   so the equation forces `F = 0` on `S`. Together with step 1, this gives
   `CanonicalEuclideanScalarEllipticAnalyticityStatement d r` for all `d r`.
3. **Coordinate transport.** The published
   `euclideanScalarEllipticAnalyticityTransport E d r` turns canonical
   regularity into the generic assertion on `E`. It uses the continuous linear
   equivalence `D.euclideanCoordinates` from `E` to
   `EuclideanSpace ℝ (Fin d)`. That equivalence carries the operator's own
   basis to the canonical basis. It transports the full action, coefficient
   analyticity, the principal symbol, smoothness and the equation to
   Euclidean coordinates. Analyticity then comes back to `E`
   (`ScalarEllipticAnalyticityReduction`). The transport theorem has canonical
   regularity as an explicit premise and does not depend on this theorem.

None of the four modules of this contribution sets a heartbeat option, so
they compile at default heartbeats. The theorem depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Modules of this contribution

- `Langlands.Analysis.EuclideanScalarEllipticAnalyticityDegenerate`: the
  canonical zero cases and the reduction to positive `d` and `r`.
- `Langlands.Analysis.CanonicalScalarAnalyticityFromWeighted`: canonical
  regularity from the weighted estimate, conditional and for all `d r`.
- `Langlands.Analysis.ScalarEllipticAnalyticityReduction`: generic regularity
  from the weighted estimate.
- `Langlands.Analysis.ScalarEllipticAnalyticityProof`: this module, with the
  unconditional theorem.

Published proof modules imported by Lean name are
`CanonicalScalarWeightedFactorialBoundsProof`,
`WeightedL2FactorialAnalyticity`, `ScalarEllipticAnalyticityDegenerate` and
`EuclideanScalarEllipticAnalyticityTransport`, all in `Langlands.Analysis`.
The target statement's Lean/Markdown pair and its import closure are
unchanged.

## Relation to Morrey–Nirenberg (1957)

The mathematical route is the scalar, homogeneous, interior case of
C. B. Morrey Jr. and L. Nirenberg, *On the analyticity of the solutions of
linear elliptic systems of partial differential equations*, Comm. Pure Appl.
Math. 10 (1957), 271–290. The registered source is
`provided-17e51270c6d50eab8ff7b4142058b4ec69474b21e75225ec9952a95784e8229f`,
SHA256 `61c74249e27625fd25cb0a33d3c77d90ab6b5306fc9bccddc7a6d5314229f915`.
Page numbers are printed pages, with one-based PDF pages in parentheses. See
also the Library note `notes/automorphic/elliptic-analyticity-source-map.md`.

- **§5, pp. 287–290 (PDF 17–20).** For one equation (`N = 1`, `f = 0`), the
  local uniform ellipticity (5.2) is a positive lower bound for the scalar
  principal symbol on a ball. Lemma 5.1 (p. 288) is the Fourier `L²` estimate
  for the frozen constant-coefficient operator. Lemmas 5.2 and 5.3 (p. 289)
  are the cutoff estimate and its factorially normalized form (5.9). Freezing
  the principal coefficients at the centre and bounding analytic coefficients
  as in (5.10) (p. 289) gives Lemma 5.4 (p. 290). Induction then gives (5.5)
  (p. 288). In this formalization, these steps are the published proof of
  `canonicalScalarWeightedFactorialBounds`, whose Markdown gives the
  detailed correspondence. Step 1 above uses only its conclusion. The
  supremum over `ρ ∈ [R/2, R)` of `(R - ρ)^k` times the `L²` norm is MN's
  normalized seminorm (5.4) for a scalar equation, before division by the
  factorial.
- **§2, pp. 275–277 (PDF 5–7).** Right after (5.5), on p. 288, MN derive
  analyticity from Lemma 2.3 and its corollary (pp. 276–277). Lemma 2.3
  applies the Sobolev Lemma 2.2 (p. 276) to every derivative, using the
  tensor norm (2.1) (p. 275) and the `L²` norms (2.4) (p. 276). This gives
  pointwise factorial bounds and hence a convergent Taylor series. The Lean
  proof follows the same two steps through `weightedL2FactorialAnalyticity`.
  Instead of MN's direct use of (2.6), it fixes the half-radius ball, then
  uses a local Sobolev estimate and a separate factorial-derivative
  analyticity criterion.

**Adaptations that are not from the source.**

- Only one scalar homogeneous equation is treated, at an arbitrary centre
  `x₀`, and smoothness `ContDiffOn ℝ ∞` is assumed. No mixed-order systems,
  boundary results or weak solutions are formalized.
- The hypothesis is pointwise nonvanishing of the principal symbol on an open
  set, not MN's uniform bound (5.2). The local uniform bound at `x₀` is
  derived inside the published weighted estimate.
- MN work in Euclidean coordinates. The target is stated on an arbitrary real
  normed space through the operator's own finite basis. The continuous linear
  coordinate transport of step 3 recovers the original norm and topology.
- MN do not treat the degenerate cases separately. Here `d = 0` and `r = 0`
  are settled by the elementary arguments of step 2, and the weighted
  estimate is used only when `0 < d` and `0 < r`.

## Authorship

Worker 116 wrote the Lean code of the four modules of this contribution in a
shared draft for this task. Worker 116 also wrote the weighted-to-analytic
bridge, the zero cases and the coordinate transport, which are published
separately. Worker 94 developed the weighted elliptic estimate and its
Fourier, frozen-coefficient and Leibniz prerequisites. Worker 815 developed
the local Sobolev, factorial-analyticity and analytic-coefficient results that
these use. Worker 1130 assembled the submission against the published
prerequisites and rewrote this Markdown.
