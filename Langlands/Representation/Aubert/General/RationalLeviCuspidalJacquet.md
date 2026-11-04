# Minimal cuspidal Jacquet modules inside an actual standard Levi

This internal supporting construction adapts Worker 379's published
`RationalCuspidalEmbeddingProof` to a fixed actual standard rational-point
Levi. `exists_nonzero_cuspidal_leviJacquet` proves that every irreducible smooth
representation of that Levi has a nonzero normalized Jacquet module which is
cuspidal on its smaller actual standard Levi. The group and representation
carrier universes are independent. The field may be any nonarchimedean local
field; no splitness, characteristic, positive-rank, admissibility or
finite-length restriction is introduced. The statement uses the canonical
point topology, the supplied maximal split torus, the generic cocharacter,
and the literal standard subgroup families.

The standard cocharacter and standard Levi intersection statements, closedness
of every standard radical and Levi, and local compactness and the
nonarchimedean-group property of ambient rational points are explicit inputs.
No quotient compactness, endpoint statement or ambient finite root system is
required. The restricted index set is finite because the chosen standard
Levi index is a finite set.

`unipotent_subgroupOf_levi_eq_bot` proves that a semidirect radical meets its
actual Levi trivially, using the projection's identity on the Levi and its
triviality on the radical. `descendantEmbedding` reads descendants of an
index inside a fixed finite root set. `leviIndex_descendantEmbedding` shows
that this preserves the ambient labels, and `leviIndex_univ` identifies the
full restricted root set. `unipotent_product_in_levi_of_subsets` restricts the
published fine-radical product: the first factor lies in the larger Levi by
monotonicity; the second then lies there because it is the first factor's
inverse times the original element.

The selected entry definition, `subgroupOfPullbackCoinvariantsEquiv`, is an
actual complex-linear equivalence between the coinvariants after flattening
`L.subgroupOf M` to `L` and the nested subgroup coinvariants before flattening.
It keeps vector classes unchanged. It is constructed using
`Jacquet.Localization.transportEquiv` and the literal continuous subgroup
identification `subgroupOfContinuousEquiv`. No abstract replacement of the
subgroup or quotient is made.

For the main proof, the full restricted root set has trivial radical by the
ambient semidirect decomposition. Its Jacquet module is nonzero. Choose an
index of minimal cardinality with nonzero Jacquet module. Every proper
descendant has zero Jacquet module by minimality; the descendant embedding
preserves cardinality. The published radical-product relation argument puts
all vectors of the chosen Jacquet module in every proper descendant's
relation span. Its normalizing character is trivial on that radical because
standard unipotents are limits of compact subgroups and that property
survives intersection with a closed Levi. The explicit coinvariant linear
equivalence transfers this vanishing to the actual flattened Levi, proving
`IsLeviCuspidal` with the exact ambient root labels.

The direct declaration-level dependencies of this argument are
`isSemidirectDecomposition_in_levi`,
`isSemidirectDecomposition_of_standardCocharacterStatement`,
`unipotent_product_of_subset`, `unipotent_le_parabolic_of_subset`,
`levi_le_of_subset`, `CuspidalEmbedding.mem_relations_of_subsingleton`,
`CuspidalEmbedding.closedNormalizerCharacter_eq_one_of_compactLimit`,
`isLimitOfCompactSubgroups_subgroupOf`, and
`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`.
These are existing Library results. The proof route is derived from them;
no new assertion from the original literature is claimed in this unit.

Three generic helpers prepare the subsequent embedding argument.
`exists_irreducible_quotient_of_finite` takes a nonzero smooth module finitely
generated over its group algebra, chooses a coatom of its invariant-submodule
lattice, and uses
`SmoothRep.RenardIrreducibleExistence.quotient_isIrreducible_of_isCoatom`
to obtain an actual irreducible smooth quotient. `roundTripPullbackMap`
transports a morphism through a group equivalence and its inverse, preserving
its linear map. `embedding_of_surjective_jacquet_map` applies
`General.FirstAdjointness.equiv` to a surjective Jacquet map with nonzero
target. The adjoint is nonzero and hence injective by
`Representation.IsIrreducible.injective_or_eq_zero`. That generic helper
retains the explicit unimodularity premise required by first adjointness.

The main minimal-Jacquet theorem uses no Langlands classification,
character-independence theorem or geometric lemma. The generic embedding
helper uses the actual first-adjointness equivalence just named, with its
unimodularity hypothesis and carrier sizes unchanged. This candidate does
not yet construct the rational inside-Levi induction embedding. Its compact
quotient discharge and the full support-category Jacquet-vanishing proof
remain separate obligations.
