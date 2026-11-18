# Scalar generator lifts of the actual band coefficients

`scalarGeneratorLifts_of_coefficients` retains the exact named
`CuspidalHilbertOrbitCoefficientStatement` and unitary-central-character premise.
For an actual cuspidal realization of `GL_(r+1)` and every vector of the full
actual determinant-band `L²` space, it proves the generic
`Archimedean.ScalarGeneratorLifts` predicate for the same scalar coefficient in
mixed real group coordinates. The directions are all elements of the original
`RealLieAlgebra`, mapped to their actual matrices by `realLieAlgebraToMatrix`.
The source operator is exactly the full enveloping action at
`envelopingGenerator (complexify X)`.

The generic predicate supplies one scalar function for every original vector,
with exact coefficient values, and identifies the value at the identity after
that source operator with the genuine first manifold derivative in the given
matrix direction. The proof takes the single smooth-function-valued linear map
supplied by the coefficient premise. Its full enveloping covariance is evaluated
at the identity. The published `envelopingAction_real_generator` and
`smoothDifferential_eq_mfderiv` formulas, through the identity normalization in
`CuspidalHilbertSmoothEmbedding`, identify its value with the scalar derivative.
Positive right translation keeps the original sign and the tangent direction
`gX`; at the identity this is the original matrix `X`.

This internal consequence uses the full band Hilbert vector directly and assumes
no vector derivative identity, Hilbert smooth-kernel criterion, bounded Lie
operator or density theorem. The number-field universe remains free and `GL_1`
is included. It establishes a scalar consequence of the retained premise.
