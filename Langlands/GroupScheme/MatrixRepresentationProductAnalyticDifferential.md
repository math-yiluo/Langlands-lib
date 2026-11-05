# Actual analytic differential of finite-product matrix representations

This internal construction uses the genuine evaluated scheme representation
and its derived smoothness. A finite family of invertible matrices embeds as
an open subset of all matrices with the original product topology. The
product of the units value embeddings proves this and supplies an actual
open partial homeomorphism, `matrixUnitsChart`.

`productMatrixCoordinateExtension` evaluates the actual
`productMatrixPointsHom` on the inverse of that chart. On every invertible
matrix family it agrees with the original evaluated representation. Its
values outside the chart target are irrelevant. The existing regular-function
criterion derives smoothness on the source units manifold; composing with the
chart inverse proves real smoothness on the open set of invertible matrix
families and in a neighborhood of each such point.

`analyticProductDifferential` is the real continuous linear Frechet derivative
of that extension at the identity family. The actual smoothness proof supplies
`hasFDerivAt_analyticProductDifferential`, ensuring that it is the derivative
there. It assumes no supplied derivative or regularity of the representation.
The word analytic here distinguishes real Frechet calculus from the
algebraic dual-number construction; no real or complex power-series
analyticity theorem is asserted.

The extension takes the identity family to the identity matrix.
`analyticProductDifferential_eq_of_extension` proves independence from
all values outside the open set: any ambient function agreeing with the
original representation on every invertible family has the same derivative
at the identity, with no regularity hypothesis on that alternative function.
The proof uses eventual equality on the open units neighborhood.
`analyticProductDifferential_trivial` applies this to the constant identity
matrix extension and proves that the genuine trivial representation has
zero differential.

The base ring, coefficient algebra and finite family index share a universe;
individual matrix indices are small. The coefficient algebra is a complete
normed commutative real algebra with the stated base-ring algebra structure.
No injectivity, positivity or nonempty index hypothesis is imposed.

Comparison with the separately constructed algebraic dual-number differential,
complex linearity in the complex specialization, Lie compatibility, coefficient
cohomology and automorphic occurrence remain separate obligations.
