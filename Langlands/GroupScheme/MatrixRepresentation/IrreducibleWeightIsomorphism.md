# Isomorphism classification of actual simple multiplicative-type representations

This module proves the exact fourth conjunct of the published
`MultiplicativeTypeRepresentationGaloisOrbitStatement`: two irreducible
finite-coordinate representations of an affine group of multiplicative
type are isomorphic by an actual bijective intertwining matrix if and only
if their sets of nonzero character spaces over any separable closure
are equal.

An injective actual intertwiner carries a nonzero character vector to
a nonzero vector of the same character. A bijective intertwiner has an
actual inverse intertwiner: cancel its injective matrix from the
identity composite. Therefore it preserves the full weight set.
A bijective original intertwiner remains bijective after scalar
extension and so gives equality of the extended weight sets.

Conversely, the single-orbit theorem gives a nonzero source weight, and
equality of weight sets makes it a target weight too. Over the separable
closure the multiplicative-type group is diagonalizable and source
character spaces span. The common-character intertwiner construction
therefore supplies a nonzero intertwiner over that closure. An
original-field coefficient functional, chosen nonzero on one of its
matrix entries, descends it to a nonzero actual original intertwiner.
The actual Schur lemma for stable kernel and image makes this map
bijective, proving the required isomorphism.

All intertwining and character-space tests use actual affine algebra
tests, with no reducedness or smoothness assumption. The source context
is Milne, *Algebraic Groups* (2017), Theorem 12.30 and proof, printed
pp. 241–242. The implemented uniqueness proof descends a nonzero
intertwiner by a coefficient functional rather than constructing the
entire finite-Galois equivalence of representation categories.
