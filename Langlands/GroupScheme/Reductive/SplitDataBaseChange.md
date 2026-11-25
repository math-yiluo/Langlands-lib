# Actual coordinate split data under arbitrary scalar extension

This internal module supports the unchanged étale-local splitting target
`EtaleLocalSplitReductiveStatement` (proved by `etaleLocalSplitReductive` in
`Langlands.GroupScheme.Reductive.EtaleLocalSplitProof`).
It derives scalar-extension comparisons from the previously implemented
coordinate pullback coherence and actual ambient-isomorphism transport.

The comparison first treats arbitrary equal composite maps of schemes,
then applies the scalar-tower identity for algebra maps. The resulting
ambient group isomorphism identifies the successive coordinate inclusion
with the direct inclusion followed by that isomorphism. The definition
`splitTorus.baseChangeHomScalarTowerIso` chooses such an isomorphism with
the coordinate compatibility proved in its specification theorem. Over a supplied
field this transfers the same actual full root datum, including coroots
and all lattice directions. The fibrewise statement uses the composite
coefficient map from the original ring for each supplied algebra over the
new ring.

Fibrewise maximality under arbitrary base pullback follows from the
published supplied-field-point maximality theorem and the natural
comparison of successive field pullbacks. No new structural hypothesis
is introduced.
