# Coordinate fibers for the original quotient action

At arbitrary universe `u`, fix actual `ValuationBuildingData G` over a
nonarchimedean local field, a supplied `B.PolysimplicialRealization R`,
and `hR : R.IsFaceCompatible`. The canonical vertex permutations
`R.vertexTranslateEquiv hR g` were recovered from the original
rational-point action on quotient facets in `RealizationVertexAction`.

`vertexTranslateEquiv_image_mem_facets` follows from the exact image of
each facet under that permutation. Its inverse is the canonical
permutation for `g⁻¹`, so `vertexTranslateEquiv_preimage_mem_facets`
gives facet preservation in the reverse direction.

For a supplied index permutation `σ` satisfying
`RespectsCoordinateFibers σ (R.vertexTranslateEquiv hR g)`,
`polysimplicialTranslateIso` applies the generic construction in
`PolysimplicialCoordinateFibers` to these two preservation laws.
It chooses a base vertex from the nonempty vertex sets of the
simplicial factors. The resulting polysimplicial isomorphism has
exactly the canonical vertex equivalence, as
`polysimplicialTranslateIso_vertexEquiv` proves.
`polysimplicialTranslateIso_image_iff` therefore gives the precise
facet-image comparison with the original quotient action.

`isPolysimplicialAction_iff_respectsCoordinateFibers` proves that
`R.IsPolysimplicialAction` is equivalent to the following condition:
for each rational point `g`, there is an index permutation `σ`
under which the output coordinate `σ i` of the canonical vertex
map depends only on input coordinate `i`. The earlier exact-action
criterion reduces to a polysimplicial automorphism of each canonical
vertex permutation. The generic coordinate-fiber criterion then
applies because preservation of facets in both directions is already
proved.

All results here are internal deductions from the imported Library
definitions and constructions. No external assertion is introduced.
This file constructs the simplicial factor maps only after the
coordinate permutation and its fiber condition are supplied.
It proves neither their existence for the actual action nor existence
of the actual building data or realization, and it does not establish
the unconditional root-valuation building construction.
