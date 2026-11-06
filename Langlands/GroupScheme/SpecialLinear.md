# The actual special linear group scheme

This internal derived construction defines `SpecialLinear.groupScheme n R` for a
finite index type `n : Type` and a commutative base ring `R`. It uses the explicit
coordinate ring

`R[X_(i,j)] / (det(X) - 1)`.

There are no inverse variables. The quotient entry matrix has determinant one,
so Mathlib's `Matrix.SpecialLinearGroup` supplies its inverse by the adjugate.
`SpecialLinear.homEquiv` identifies algebra maps out of this ring with all
matrices of determinant one. The inverse maps specialize the universal matrix
and classify a matrix by its entries; polynomial and quotient extensionality
prove that they are inverses. These identifications commute with algebra maps.

The construction then uses the published `Corepresented.groupScheme` to put the
actual group-scheme structure on the relative spectrum of that ring. Its
structure morphism is affine. `SpecialLinear.pointsEquiv` is a natural group
equivalence on **every** relative test scheme `T`, with values in determinant-one
matrices over `Γ(T, O_T)`. Neither affineness nor reducedness of `T` is assumed.
Its entries are exactly pullbacks of the global entry sections. The affine-test
version takes values directly in the original test algebra, and its inverse is
the spectrum of the matrix's classifying algebra map.

`SpecialLinear.inclusion` is the actual morphism into the published general
linear group scheme, induced by the natural entrywise inclusion of
determinant-one matrices into invertible matrices. Its action on every test
scheme is the usual matrix inclusion.

The provenance is elementary quotient algebra and the published corepresented
group construction. This supplies actual rank-one coordinates needed to compare
the homogeneous-polynomial representation with covariant functions. It does not
assert simple connectedness, identify a full induced coordinate space, or prove
the general Steinberg big-cell statement.
