# Topology of actual changes of adelic level

The theorem `Langlands.Global.adelicLevelModelTransitionTopology` proves
`AdelicLevelModelTransitionTopologyStatement` in an arbitrary common universe.
For finite-type models over actual S-integers, the original transition for
S contained in T is continuous and open. If the original model is separated,
it is an open embedding. The curve-place clause retains arbitrary constant
fields, a compatible rational-function-field action and the FunctionField
hypothesis. The full number-field clause retains every infinite place.
Neither clause requires an affine or separated model for continuity or
openness. All finite S and T are allowed.

This implements the final assertion of Conrad's Theorem 3.6, printed
pp.6–8 of *Weil and Grothendieck approaches to adelic points* (2011),
with the derived arithmetic scope explained by the target statement.
The maps and topologies are the original published constructions.
Model descent, model independence, composition and global adelic colimits
remain separate obligations.

The supporting module `AdelicLevelModelTransitionLocal` constructs the
actual local maps and proves their equality with the original transition
in the original coordinates. Each is continuous and, in local finite type,
open by composition of coefficient extension and base-change point
homeomorphisms. The open units these lemmas need in every local factor
come from the published theorem `adelicLocalFactorUnits`.
The local coefficient inclusion is an open embedding:
at newly inverted places it is the original valuation-subring inclusion,
and at other places it is the identity after matching the underlying place.
At unchanged places the local point map is bijective. The exceptional
indices form a finite set. Reduced local rings and separatedness give
injectivity of every local point map.

The generic coordinate lemma reindexes the product through the equivalence
of actual place indices. Continuity follows coordinate by coordinate.
The product open-map theorem applies because only finitely many local
maps can fail to be surjective. The finite-type arithmetic coordinate
homeomorphisms then transfer continuity and openness to the original
transition. These are the published
`curvePlaceLevelModelPointMap_isHomeomorph_of_finiteType` and
`numberFieldLevelModelPointMap_isHomeomorph_of_finiteType`, applied to
both the source and the target models.
Finite type of the target model follows by pullback of the
original structure morphism. A second coordinate lemma uses source
coordinate injectivity and all local injections to prove injectivity of
the original transition. A continuous, injective, open map is an open
embedding. These arguments apply to both arithmetic families, including
the unchanged infinite factors in the number-field case.
