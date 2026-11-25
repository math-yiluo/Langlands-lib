# Inversion in an actual E7 pinning

This internal derived helper uses the published E7 Cartan rigidity certificate and the
published projection of full root-datum automorphisms modulo the Weyl group.
The hypotheses specify every ordered Cartan entry and full integral coroot span.
The projected negation fixes all simple vertices by E7 rigidity, so it is the identity
on the entire root datum. The projection kernel criterion then puts negation in the
Weyl group. The actual root-datum comparison realizes its full character action by
a rational normalizing point of the supplied split maximal torus.

The three lemmas are `SplitPinning.negAut_mem_weylGroup_of_E7`,
`exists_normalizer_negates_characters_of_E7`, and
`exists_normalizer_inverts_torus_of_E7`. They apply over any field and do not
require the field to be algebraically closed. The final lemma compares torus
morphisms using all characters of the supplied split torus. The character action
uses the inverse normalizing automorphism, so the inverse normalizer point
realizes `SpecialLinearTorusAutomorphism.negIso` itself. This is inversion on the
entire torus, including points on nonreduced test schemes.

The entry proposition `Langlands.GroupScheme.SplitPinning.E7TorusInversionStatement` records the precise scope of
`exists_normalizer_inverts_torus_of_E7`: its explicit hypotheses are universally quantified in a
Prop-valued definition. The implemented theorem and proof are retained.
This module is given as a statement because its mathematical entry is
a proposition, rather than a data construction.
