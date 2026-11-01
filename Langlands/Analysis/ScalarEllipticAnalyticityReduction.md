# Reduction of generic scalar regularity to weighted estimates

This helper module of `Langlands.Analysis.ScalarEllipticAnalyticityProof`
proves `scalarEllipticAnalyticity_of_weightedFactorialBounds`. It takes
`CanonicalScalarWeightedFactorialBoundsStatement d r` for every `d r : ℕ` as
an explicit premise. The conclusion is the unchanged published
`ScalarEllipticAnalyticityStatement E d r`. This holds for every real normed
space `E : Type v` in an arbitrary universe, in its original norm, and for
every `d r : ℕ`, including zero.

## Proof

The premise gives canonical Euclidean regularity
`CanonicalEuclideanScalarEllipticAnalyticityStatement d r` through
`canonicalEuclideanScalarEllipticAnalyticity_of_all_weightedFactorialBounds`
(module `Langlands.Analysis.CanonicalScalarAnalyticityFromWeighted`). The
published theorem `euclideanScalarEllipticAnalyticityTransport E d r` (module
`Langlands.Analysis.EuclideanScalarEllipticAnalyticityTransport`) has
canonical regularity as its explicit premise and gives the generic assertion
on `E`. It works through the operator's actual basis: it uses the continuous
linear equivalence from `E` to Euclidean coordinates and transports the full
action, the coefficients, the principal symbol, smoothness and analyticity.
It does not use the generic theorem proved here, so this reduction is not
circular.

A closing `example` restates the theorem's complete type, quantified over the
estimate, `E` with its instances, `d` and `r`, and checks it against the
theorem.

## Provenance

Coordinate transport is an internal adaptation. Morrey–Nirenberg (1957) work
in Euclidean coordinates, while the target assertion is stated on an
arbitrary real normed space through the operator's own finite basis.
Worker 116 wrote the Lean code in a shared draft for this task, and Worker 1130
rewrote this explanation for submission.
