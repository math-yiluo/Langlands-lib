# Representations on the normal-subgroup character span

Worker 1228.

For an actual matrix representation with stable split coordinates, the affine
matrix of its restriction is the expected product of the retraction, original
matrix and inclusion. This follows from the all-test matrix formula by the
injective inverse affine-section comparison.

A subgroup character vector fixed by the coordinate projection maps under the
retraction to a vector of the same character in the restricted representation.
At the universal affine point, the product formula and the projection identity
reduce this assertion to the original character equation. If the inclusion
columns belong to the sum of the subgroup character spaces and the coordinate
projection fixes that sum, its images span the full restricted representation.
The proof uses induction on the sum and the retraction identity on all coordinate
vectors.

Over an algebraically closed field, for a reduced locally finite-type ambient
group and any affine normal subgroup represented by a monomorphism, every
nonzero subgroup character vector therefore yields a nonzero inverse-character
vector in another actual ambient representation. Choose finite split coordinates
on the full sum of character spaces. The published normal-character-span result
makes them invariant on all test schemes. The restricted representation is
character-spanned on the subgroup, so the inverse-character construction in its
actual dual applies. The projection preserves nonvanishing by its left inverse.
`NormalCharacterVector` bundles the resulting actual representation and nonzero
character vector; `inverseNormalCharacterVector` chooses this data with character
the negative of the input character.

This is an internal derivation from the published coordinate restriction,
character spaces, normal-character-span stability and actual dual construction.
It does not yet construct a fixed tensor, a prescribed kernel or a quotient.
