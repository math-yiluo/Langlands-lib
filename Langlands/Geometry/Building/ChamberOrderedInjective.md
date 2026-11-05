# Ordered chamber and facet block embeddings from the Dynamic root product

This internal construction restricts an ordered product of the actual relative
root subgroup functors to the existing chamber and facet blocks. It provides
embeddings with exactly the existing `orderedChamberBlockProduct` and
`orderedFacetBlockProduct` as their underlying functions.

The results are conditional on the published
`RelativeRoot.DynamicRootOrderedProductStatement` at the same arbitrary universe
`u`. This statement is a premise here, not a theorem established by this unit.
The ambient group is connected reductive over a field in universe `u`, and the
chosen torus inclusion is a maximal split torus. The order `a : Fin n → X*(S)`
may be any injective enumeration whose range is exactly the indivisible positive
actual roots of the chosen cocharacter. There is no extra geometric assumption
on the apartment point or subset, and both `strict = false` (depth `0`) and
`strict = true` (depth `0+`) are covered. Substituting the negative cocharacter
covers the negative root order.

The general lemma `orderedSubgroupPoints_injective_of_mono` works over any base
scheme and on every test scheme. It assumes actual representing group schemes
for the factors and that their ordered multiplication morphism is monic. Each
subgroup point is lifted with the published represented-point equivalence.
The finite-product point equivalence reassembles the lifted coordinates.
The published formula for evaluation of ordered multiplication identifies its
value with the list product in the given order. Cancellation of the monomorphism
identifies the reassembled points; taking coordinates identifies all original
subgroup points.

`orderedRootSubgroupPoints_injective_of_statement` obtains these hypotheses from
the explicit Dynamic statement. That statement supplies an isomorphism from the
product of representing root factors to a representative of the Dynamic
unipotent group. Its inclusion into the ambient group is monic, so the specified
ordered multiplication is monic. This yields injectivity on all tests, including
rational points.

The chamber and facet restrictions use the published equalities between each
actual doubled-root block and its corresponding depth subgroup. Those
equalities retain the doubled-root factor in the definition and prove its
containment using the intrinsic root inclusion and valuation axiom V4. The
depth subgroups lie in the actual root groups by their original definitions.
Restricting an injective product to these subsets gives the two embeddings.
The empty index set and the empty apartment subset retain their published
definitions and are included.

This unit proves no exact range or chamber factorization statement. In
particular it does not prove `DynamicRootOrderedProductStatement`, sharp or full
Iwahori product ranges, equality of full and sharp unipotent intersections, or
the central and normalizer intersections. Its provenance is the internal
argument above using the existing represented-point and ordered-product
interfaces, and the already published block identities. It makes no additional
literature claim.
