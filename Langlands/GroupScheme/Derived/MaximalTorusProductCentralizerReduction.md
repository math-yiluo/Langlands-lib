# Derived multiplication from maximal-torus selfcentralization

Authors: Worker 1447 and Worker 1667.

This internal reduction proves
`DerivedMaximalTorusProductCentralizerReductionStatement`, the implication from
the existing `MaximalTorusCentralizerStatement` to the unchanged
`DerivedMaximalTorusProductSurjectivityStatement`. The former statement remains
an explicit premise. The latter is not proved unconditionally here.

The stronger local construction
`IsDerivedSubgroup.smoothSurjective_product_of_split_selfCentralizing` works in
any smooth connected affine group over any field. It takes a supplied actual
full derived inclusion `d` and a closed split torus inclusion `i` whose all-test
centralizer equals its range. It does not require reductivity or maximality.
The existing derived smoothness theorem makes the first factor smooth; split
tori are smooth. The derived and torus tangent submodules span the ambient Lie
module by `IsDerivedSubgroup.tangentSubmodule_range_sup_selfCentralizing_torus_eq_top`.
That result places every nonzero torus weight in the derived tangent and the
zero weight in the selfcentralizing torus tangent. Both inclusions are actual
linear differential ranges because the closed subgroup maps are monomorphic.
Normality of the derived subgroup then lets
`smoothSurjective_subgroupProductMap_of_normal_of_tangentSpan` prove smoothness
and scheme surjectivity of the ordered product map.

`IsDerivedSubgroup.smoothSurjective_product_of_selfCentralizing` removes
splitness. It chooses the splitting field contained in the supplied `IsTorus`
witness. The derived inclusion remains a full derived inclusion after that
field extension. The explicit selfcentralization equality also survives base
change, as do closedness and smoothness. The ambient smooth connected affine
group stays connected over the extension. Thus the split construction applies,
and the published field-extension descent theorem for subgroup multiplication
returns smoothness and surjectivity of the original morphism.
No assertion about maximality after base change is needed in this argument.

Finally, the assumed maximal-torus centralizer statement supplies precisely the
selfcentralization equality for the target's connected reductive ambient group
and specified maximal torus. Its other hypotheses supply smoothness, affineness,
connectedness, the torus predicate, and closedness. Applying the local result
and taking its surjectivity component gives the exact target conclusion. All
fields, characteristics, and common universes are retained.

Every product used here is the actual ordered morphism `D × T → G`, sending
`(x,t)` to `d(x)i(t)`. The base-change helper calls it `subgroupMultiplication`,
which is the same expression as `subgroupProductMap`. Surjectivity concerns
underlying scheme points; no surjectivity on ground-field rational points is
asserted.

The provenance is internal composition of the paired tangent-spanning and
normalized-multiplication constructions with the published derived smoothness,
derived base change, centralizer base change, geometric connectedness, and
ordered multiplication descent results. Worker 1667 authored the reused tangent
helper. Proving maximal-torus selfcentralization remains a separate structural
obligation before this reduction can discharge the full proof task.
