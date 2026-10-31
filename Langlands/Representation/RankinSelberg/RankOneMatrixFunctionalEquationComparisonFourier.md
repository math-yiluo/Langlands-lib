# Row and matrix Fourier transforms at actual rank one

This is an internal coordinate comparison for the rank-zero branch of
`RankOneMatrixFunctionalEquationComparisonStatement`. It uses the published
`oneByOneRow` homeomorphism from `RankOneMatrixWhittakerComparisonZero` and
Mathlib's product-measure theorem `measurePreserving_piUnique`.

`oneByOneSchwartzEquiv` is the complex linear equivalence from row tests to
matrix tests given by pullback through `oneByOneRow`; its inverse pulls back
through the inverse homeomorphism.

`oneByOneRow_measurePreserving` proves that taking the unique row sends the
`1 × 1` rectangular product measure to the one-coordinate row product measure.
Both use precisely the supplied additive Haar measure `ν`. The proof uses the
singleton outer index of the product; it introduces no volume factor.

`rectangularPairing_oneByOneRow` identifies the entrywise matrix pairing with
the row pairing. `rectangularFourierIntegral_oneByOneRow` then transports the
actual Bochner integral through the measure-preserving homeomorphism and
commutes the two complex factors in the integrand. It applies to arbitrary
functions, using the usual totalized Bochner integral on both sides.

`matrixFourierPair_oneByOneRow_iff` applies this identity to Schwartz–Bruhat
tests. The forward direction transports the actual Fourier-value identity;
the reverse direction also supplies matrix-integrand integrability from the
published compact-support argument. The scalar measure is sigma-finite in
this last theorem, as required by that argument; the canonical matrix product
measurable space is assumed to be a Borel space. The result uses neither
self-duality nor a special conductor normalization and therefore applies to
every additive character for which the declared character structure exists.

These are derived coordinate facts, rather than assertions of analytic
existence or of the gamma comparison. They supply only the row/matrix Fourier
compatibility needed for the separate Tate argument described in the target's
Markdown, following JPS 1979, printed page 181. No signed higher-rank Weyl
conversion is asserted here.
