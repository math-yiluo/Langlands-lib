# Finite vertex fixer approximation over the actual maximal unramified field

`Langlands.Geometry.Building.MaximalUnramified.finiteVertexFixerApproximation.{u}`
proves exactly the existing `FiniteVertexFixerApproximationStatement.{u}`, at
arbitrary universe `u`, with all its original quantified inputs and no additional
hypothesis. For a nonempty affine bounded subset of an apartment translated by
`g`, it supplies a nonempty finite set of actual building vertices whose common
norm-one fixer is contained normally and with finite index in the norm-one
pointwise fixer of the original subset.

The proof is an internal composition of published results.
`MaximalUnramified.exists_order_eq_one F` supplies a unit of source-positive
order one for the prescribed normalized valuation on `inertiaFixedField F`.
It is the image of a base-field uniformizer. The supplied
`C : MaximalUnramified.BuildingData F G` is definitionally integer-valuation
building data over that same field. Consequently
`IntegerValuationBuildingData.isAffineRootSystemWithRankZero_affineRoots`
applies to `C` and this unit witness, proving the corrected affine-root-system
predicate, including rank zero.

For this root system,
`IntegerValuationBuildingData.smul_apartmentMap_eq_of_vertices_fixed`
proves that an original rational element fixing all vertex images of a closed
facet fixes its entire image in the quotient building. That result derives
two-point fixation from actual unipotent and normalizer decompositions, then
uses convexity and the finite-vertex convex-hull description. It supplies the
closed-facet premise of
`IntegerValuationBuildingData.finiteVertexFixerApproximation_of_closedFacetsFixedByVertices`.

The latter theorem constructs the finite vertex set as the image under
`x ↦ g • C.apartmentMap x` of all vertices of the closures of the facets meeting
the original apartment subset. Affine boundedness makes this set finite;
nonemptiness of the subset makes it nonempty. Closed-facet fixation gives the
required containment of the intersection of vertex one-stabilizers in the
original norm-one pointwise fixer. That fixer preserves the finite vertex set,
and its finite permutation action has the common vertex fixer as kernel.
This gives normality and finite index for exactly the subgroup specified in the
target.

All groups, apartment maps, vertices and quotient actions are the original
ones in the statement, and the character-valuation kernel uses
`MaximalUnramified.valuation F`. Local-field structure is used only on `F`;
the extension field retains its prescribed valuation. The source correspondence
with KP 8.3.1--8.3.2 is recorded in the unchanged statement's paired Markdown.
This proof discharges the finite-approximation proposition only.
