# Rank-one comparison along a supplied reciprocity candidate

This internal construction and comparison API uses the published actual
rank-one Weil and automorphic class spaces. The field, parameter-carrier and
automorphic-carrier universes remain independent.

`exists_rankOneWeilFieldCharacter` takes an arbitrary rank-one continuous
irreducible Weil class and a supplied reciprocity candidate. A representative
of its actual quotient has complex dimension one. The published
`Weil.representationCharacterNormalization` supplies a continuous character
and an equivalence from that representation to its scalar model.
`LocalFactor.RankOne.fieldCharacter` transports the character to field units;
the published inverse identity `weilCharacter_fieldCharacter` identifies
its pullback with the original character. Reversing the representation
equivalence proves the existing `IsRankOneWeilCharacter` relation.
`rankOneWeilFieldCharacter` chooses such a field character, and its `_spec`
theorem records that relation.

For uniqueness of classes represented by the same character, the proof
composes one scalar-model equivalence with the inverse of the other.
The existing quotient equality criteria identify the resulting actual
representation classes. Forgetting the continuity/irreducibility and rank
certificates is injective, as is forgetting supercuspidality. These
injections give the Weil and supercuspidal uniqueness statements.

`supercuspidalRankOne_eq_of_compatibility` chooses the field character for
each given rank-one Weil class. Each family's rank-one compatibility
supplies a Weil class and a supercuspidal class for this same character.
Weil-side uniqueness identifies both supplied Weil classes with the
original class. Automorphic-side uniqueness then identifies the two
images. Function extensionality gives equality of the rank-one maps.

The provenance is internal: all objects and relations are already
published, and the new choice and comparisons follow from their proved
normalization and quotient APIs. No new assertion is attributed to the
literature. The result assumes a common supplied reciprocity candidate
and the two displayed compatibility predicates. It proves neither
existence nor uniqueness of reciprocity candidates, existence of
compatible families, nor the supercuspidal correspondence in higher rank.
