# Complex Levi-compatible Iwasawa from ambient star realization

Author: Worker 1655.

This internal construction shows that over an algebraically closed `RCLike`
field, an ambient closed star-stable realization suffices to accommodate a
specified dynamic parabolic and Levi. Star stability of the specified Levi
is no longer an input. The coefficient field has arbitrary universe `u`.

`MatrixRepresentation.HasClosedStarRealization G` is a proposition saying
that some representation of the actual group scheme on `Fin d` is a closed
immersion and its actual base-field affine matrix-point image is stable
under conjugate transpose. The predicate contains no compact subgroup,
cocharacter, parabolic, Levi or decomposition.

`HasClosedStarRealization.hasHermitianStarLeviRealization` takes a common
actual cocharacter `χ` whose dynamic parabolic and dynamic centralizer are
represented by the two supplied morphisms `p` and `m`. Apply the internal
cocharacter construction to the closed star-stable representation `ρ`.
It supplies a matrix `g` in the actual image such that the weights of
`χ` composed with the conjugated representation are Hermitian. Composition
with the inner scheme automorphism preserves closed immersion. Conjugation
by `g` preserves the point image because `g` itself belongs to that image.
The conjugated representation therefore remains star-stable. The same
`χ`, `p` and `m` provide the required dynamic pair; none is replaced.

`HasClosedStarRealization.hasDiagonalStarLeviRealization` composes this
result with unitary diagonalization of Hermitian cocharacter weights.
`HasClosedStarRealization.hasLeviCompatibleDecomposition` then applies
the compatible diagonal polar construction when the ambient scheme is
affine. It constructs a compact subgroup satisfying ambient maximal
compactness, ordered parabolic-image-times-compact coverage, equality of
the parabolic and Levi intersections with the compact, and maximal
compactness of the inverse image on the specified Levi point group.
The point groups retain their regular-function evaluation topologies.

The provenance is internal composition of internal cocharacter
unitarization, image-preserving matrix conjugation, and the existing
Hermitian and diagonal Iwasawa constructions. No new assertion is
attributed to an external source. Initial closed star-realization existence,
existence of the common cocharacter for an arbitrary rational pair, and
the real-coefficient case remain obligations of the full archimedean
existence task. This module does not prove the unconditional target.
