# Unitary intersections for a compatible diagonal dynamic Levi

Author: Worker 1655.

This internal prerequisite defines `Dynamic.IsDiagonalLeviPair` for a fixed
closed matrix representation, cocharacter, parabolic inclusion and Levi
inclusion. The cocharacter maps to the diagonal cocharacter in that same
representation, and the inclusions represent its dynamic parabolic and
centralizer. Existence of such compatible data remains a separate obligation.

A unitary matrix belonging to a weight-block parabolic is weight-block
diagonal: its inverse is its conjugate transpose, and the inverse still
belongs to the parabolic. The two triangular vanishing conditions therefore
kill every entry joining distinct weights. Conjugate transpose preserves
the weight-block diagonal condition.

The actual affine point membership lemmas apply the published closed-subgroup
pullback identities and the diagonal cocharacter classifications. They transfer
matrix entries from the global sections of the affine test scheme to the
test algebra through its canonical section isomorphism. Injectivity and
preservation of zero give both directions.

For a pair satisfying `IsDiagonalLeviPair`, these tests apply to the literal
ranges of the specified parabolic and Levi point homomorphisms over any
test algebra. Over an arbitrary-universe `RCLike` field, with matrix indices
`Fin d`, `IsDiagonalLeviPair.range_inf_unitarySubgroup` proves that these
two ranges have exactly the same intersection with the inverse image of
the standard unitary group. The forward direction uses the unitary
block-parabolic lemma; the reverse direction uses the block-diagonal
vanishing condition.

`IsDiagonalLeviPair.restrict_star_stable` assumes that conjugate transpose
preserves the ambient matrix image. For an actual Levi point, choose an
ambient point representing the conjugate transpose of its matrix.
Block-diagonal stability places this point back in the literal specified
Levi range. Choosing its preimage proves conjugate-transpose stability
for the restricted representation. This argument does not identify the
Levi carrier with its image. `unitarySubgroup_restrict` records the
definitional equality between its unitary subgroup and the inverse image
under the actual Levi point homomorphism.

These are elementary derived results using the existing subgroup and actual
scheme-point constructions. They do not assert general self-adjoint
realization, compatible cocharacter existence, or the full archimedean
Iwasawa proposition. Compactness, unrestricted maximality and parabolic
covering are not conclusions of this module; these require the separate
polar and topological constructions.
