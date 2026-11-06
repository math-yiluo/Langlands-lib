# Actual rank-one correspondence along supplied reciprocity

This internal construction takes a reciprocity candidate for the actual
local Weil group as an explicit input. It produces an equivalence between
the existing continuous irreducible rank-one Weil classes and the existing
supercuspidal GL₁ classes. The field, Weil-carrier and automorphic-carrier
universes remain independent.

The Weil class of a continuous field character is the published
`FiniteRepresentation.continuousIrreducibleCharacterClass` of its continuous
pullback. This constructor uses the actual lifted complex line, with its
proved continuity, irreducibility and rank. Its scalar-model equivalence
proves the existing `IsRankOneWeilCharacter` relation. Character uniqueness
and injectivity of pullback prove injectivity of this class map. The
published rank-one Weil character normalization and inverse character
transport give surjectivity through
`exists_rankOneWeilFieldCharacter`, followed by uniqueness of the class
with a fixed scalar character.

Inverting this equivalence and composing with
`rankOneSupercuspidalCharacterEquiv` gives `rankOneReciprocityEquiv`.
The inverse identities show that the image of the class of a pulled-back
character is its constructed genuine supercuspidal GL₁ class.
Uniqueness for a fixed Weil character extends this specification to every
class satisfying the same scalar-character relation.

The final theorem identifies the existing
`SupercuspidalRankOneCompatibility` predicate for an arbitrary rank-indexed
map with equality of its rank-one component and this constructed bijection.
For the forward implication, every Weil class is a pulled-back character;
uniqueness of its Weil class and of the resulting supercuspidal character
class identifies the two images. For the reverse implication, the
constructed Weil class supplies the required existential witness.

No reciprocity candidate is constructed. Geometric normalization is the
normalization of the supplied candidate when it satisfies the separate
reciprocity relation. No higher-rank correspondence or determinant,
twist, dual, L-factor or epsilon-factor compatibility is asserted here.
