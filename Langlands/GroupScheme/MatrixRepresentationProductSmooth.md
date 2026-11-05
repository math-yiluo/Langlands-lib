# Smooth evaluation of actual finite-product matrix representations

This internal construction applies the actual finite group-scheme product
smoothness criterion and the actual general-linear regular-function criterion
to an existing genuine scheme representation.

For any finite family of small finite matrix indices over a commutative base
ring, let the test algebra be a complete normed commutative real algebra with
its specified base-ring algebra structure. The base ring, test algebra and
finite family index share universe `u`; the chart model and parameter space
retain independent universes.

`coordinateSmooth_affineMatrixEquiv_symm` takes real smooth families in each
actual matrix-units manifold and assembles their inverse affine coordinates
into a coordinate-smooth family of points of the categorical product scheme.
It uses the identity coefficient map, the single-factor GL equivalence and
the product assembly theorem. No manifold on arbitrary scheme points is used.

`contMDiff_productMatrixPointsHom` then postcomposes those actual points with
the underlying morphism of a genuine `MatrixRepresentation`. Pullback of
global regular functions preserves coordinate smoothness. The target GL
criterion gives real smoothness of the actual evaluated invertible matrix.
The map being proved smooth is precisely the published
`productMatrixPointsHom`, not an independently supplied homomorphism.

Empty factor and matrix indices are allowed. This construction proves no
identification of analytic and algebraic differentials.
