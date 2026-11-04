# The irreducible test for a finite-family ambient projector

This internal construction uses a topological group `G`, a normal subgroup `N` with its inherited topology, and a supplied finite family `E i` of irreducible compact-coefficient smooth complex representations of `N`. Injective intertwiners from the family into the restriction of a smooth ambient object `A` must span that restriction. The intrinsic isotypic subrepresentation and annihilator for every selected class must be complementary in the restrictions of `A` and of each object on which the projector is constructed.

`finiteFamilyAmbientProjector` is the existing selected projector regarded as an actual ambient intertwiner. The finite spanning family supplies conjugation stability through the published inverse-conjugation theorem, so stability is not an additional input. The construction is idempotent and natural for all ambient intertwiners, and it fixes every vector of `A`. The group universe, compact representative universe, ambient carrier universes and finite indexing universe are independent.

For an ambient irreducible object `X`, `finiteFamilyAmbientProjector_fixes_iff_restricted_hom` identifies identity action of this projector with the existence of a nonzero actual intertwiner from the restriction of `X` to the restriction of `A`. No irreducibility of `A`, semisimplicity or finite length of the restriction of `X` is assumed.

For the forward implication, choose a nonzero vector of `X`. If the projector fixes it, it cannot belong to the selected common annihilator. Thus some map to a compact representative of a selected class does not kill it. Identify that representative with a member of the supplied family and follow the map by the family's injective map into `A`. The composite remains nonzero.

For the reverse implication, the finite spanning family makes the projector on `A` the identity. Naturality of the subgroup projector along a nonzero restricted intertwiner shows that the ambient projector on `X` cannot be zero. An endomorphism of an irreducible representation is injective or zero, so this projector is injective. Its idempotence then implies identity action.

The provenance is internal composition of the published selected-projector, conjugation, class-representative and irreducible-intertwiner APIs. This result does not construct a finite restriction family for rational-point representations or prove the equivalence between restricted intertwiners and unramified twists. Those are separate inputs to the rational inertia application.
