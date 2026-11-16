# Actual equivariant line bundles on étale equivalence relations

This internal interface records the actual sheaf data needed for polarized
scheme descent, independently of any presheaf of families. It builds only on
`EtaleEquivalenceRelation` and `LineBundle`.

`EtaleEquivalenceRelation.Related a b` means that the two morphisms from the
same scheme to the chart are the projections of a morphism to the relation
scheme. This is a proposition about all scheme-valued points, using the
actual relation scheme.

`Picard.EquivariantLineBundle E` consists of an actual line bundle `B` on the
chart and an isomorphism `a*B ≅ b*B` for every related pair. These
isomorphisms are identities on equal pairs, satisfy the transitivity law,
and commute with arbitrary precomposition. The latter law includes both
canonical composition isomorphisms of actual pullback functors. Relatedness
witnesses are proofs of a proposition, so the transport has no dependence on
a choice of relation witness. The laws are stated for every supplied
relatedness proof, including the one for the composite pair.

The definition packages coherent transport and makes no effectivity claim.
Evaluating it on the two projections gives the usual isomorphism on the
relation scheme. The all-test presentation is used here so that a coherent
line bundle on a presheaf supplies the datum directly, without replacing
actual line bundles or their isomorphisms by classes.
