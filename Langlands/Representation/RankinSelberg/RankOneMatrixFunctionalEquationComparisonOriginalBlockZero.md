# The actual original block-zero integral from matrix analytic data

Worker 396. Internal derived prerequisite for the matrix functional-equation
comparison. All original field and representation-carrier universes remain
independent. No original-source transcription is asserted.

`unequalRankIntegralAt_eq_rankCast` exposes the type transport of the literal
`unequalRankIntegralAt` wrapper: it equals the actual unequal-rank integral of
the first Whittaker function transported along the supplied rank equality.
It changes neither the second function nor either measure.

`unequalRankIntegralAt_rankOne_one` identifies the literal original block-zero
integral of a representation on `GL_(m+2)` with

```text
integral_GL1 W(diag(det g,1,...,1)) |det g|^(s-(m+1)/2) dg.
```

The second vector is `rankOneTrivialModelOne`, the actual constant-one vector
in the trivial rank-one coefficient model. The block parameter `k` is any
natural number satisfying the literal rank equality; that equality forces
`k=m`. The rectangular measure is exactly `rectangularMeasure nu 0 1`, and
its published zero-row identity makes it unit point mass. Every compatible
quotient measure equals the transported normalized `GL1` Haar measure.
The proof removes these two integration wrappers and applies the published
rank-cast integrand identity. The integral equality holds at every complex
parameter for the totalized integrals, with no convergence assumption.

`unequalRankConverges_rankOne_one_iff` also identifies absolute convergence.
It uses the measurable equivalence of a product with a one-point matrix
space and the measurable equivalence of the rank-one quotient with `GL1`.
Pointwise equality of the actual integrands then gives integrability in
both directions. In particular, the value equality does not substitute for
an absolute-convergence argument.

The p-adic specialization uses the canonical field topology, valuation and
Borel structures, and retains the supplied additive Haar measure `nu` and
any compatible quotient measure `mu`.
`PadicOriginalBlockZero.AnalyticAssertions` is a Prop-valued packaging of a
common right half-plane for the actual original block-zero integrals with
the canonical second vector, and a rational continuation for each first
model vector. Its continuation uses exactly the literal block parameter
`(m+1)-0-1` required by the positive-rank gamma assembly.

`convergesOnRight_of_matrix` obtains the same common half-plane from the
published BoxConvergence theorem and transfers it through the convergence
identity. `rationalContinuation_of_matrix` transfers the published original
rank-one continuation through the exact integral identity.
`analyticAssertions_of_matrix` combines these results. Their only analytic
premise is the actual matrix convergence or matrix analytic assertions of
`glModelRepresentation` on the specified coefficient image, together with
smoothness of the original representation and compatibility of `mu`.
They require no extra original rank-one convergence, rationality,
irreducibility, finite length, self-duality or functional equation.

The proof reuses published actual rank-one quotient compatibility and
uniqueness, zero-row point mass, rank-cast integrands, the canonical second
model vector, and the positive-volume box convergence transfer. The genuine
dual integral, paired Fourier extraction, normalized equation and final
all-rank gamma comparison remain later obligations.
