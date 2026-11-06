# Uniqueness of the extended negative-rho character

For a supplied closed representative `H` of a dynamic parabolic in a
separated group scheme over an arbitrary base, and a supplied commutative
representative `T` of its dynamic centralizer,
`parabolicCharacterLatticeEquiv` identifies all rational characters of `H`
with the character lattice of `T`. It composes the restriction equivalence
of `Dynamic.ParabolicCharacters` with the existing identification of
rational characters of a commutative group scheme and its character lattice.

`parabolicCharacterLatticeEquiv_symm_eq` shows that the inverse is exactly
the existing `extendCentralizerCharacter` map. This equality is definitional:
both maps compose a centralizer character with the actual limit morphism.
The inverse law gives `character_eq_extendCentralizerCharacter`, stating
that each parabolic character is the extension of its own restriction,
and `extendCentralizerCharacter_surjective`. These conclusions retain the
closedness hypothesis that is absent from the earlier one-sided extension
construction and injectivity proof.

Over a field, suppose a root datum on the supplied centralizer lattices,
a base of that datum, and integral generation by its coroots are supplied.
`eq_negativeRhoCharacter_iff` proves that a rational character of `H` equals
the existing `negativeRhoCharacter` precisely when its centralizer
restriction corresponds to the negative of `IntegralWeylVector.rho`.
The forward implication uses the existing restriction formula. The reverse
uses injectivity of the two restriction identifications. The ambient group
is assumed affine here, supplying separatedness.

This is a derived compatibility and uniqueness result, using the existing
limit extension and the proved character-restriction equivalence. It
constructs no root datum or integral coroot-generation proof; the supplied
datum need not be asserted to be the actual root datum to obtain this
identity. It supplies no negative-rho eigenvector, covector or coordinate
on the ambient group. Those existence obligations and the universal
Steinberg big-cell theorem remain separate.
