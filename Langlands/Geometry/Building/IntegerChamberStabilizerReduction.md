# Chamber stabilizers reduce to the apartment normalizer

This is an internal reduction for `IntegerValuationBuildingData v G` over an
arbitrary field `k`. Its inputs are the actual integer-valued KP apartment and
quotient, with the connected reductive and maximal split torus hypotheses already
contained in the datum. It does not assert a simply connected normalizer theorem.

`ChamberNormalizerFixing` is the proposition that every element of the original
normalizer preserving an apartment chamber fixes every point of that chamber.
This is an internal property of the existing apartment action, rather than a
claim that the property holds for all building data.

The provenance is the published
`IntegerValuationBuildingData.exists_normalizer_eq_on_translated_facet` and
`normalizer_smul_isFacet` in `IntegerBuildingFacetPartition`. Those results derive
the required root doubling and facet preservation from the root valuation data.
No additional building axiom, local field assumption or apartment injectivity
assumption enters this reduction.

`exists_normalizer_stabilizes_eq_on_translated_facet` starts with a rational
element `g` preserving the image of an apartment facet `Fa` translated by `h`.
Choose a point `a` of `Fa`. Preservation supplies a point `b` of `Fa` with
`g · (h · apartmentMap a) = h · apartmentMap b`. The published coordinate-change
lemma supplies a normalizer element `n` that sends `a` to `b` and agrees with
`h⁻¹ g h` on the image of every point of `Fa`. The two apartment facets
`n · Fa` and `Fa` share `b`, hence are equal. Translating the agreement by `h`
proves the stated agreement on the translated facet.

`mem_pointwiseFixer_of_stabilizes_chamber_of_normalizer_fixing` assumes that every
normalizer element preserving any apartment chamber fixes that chamber pointwise.
Write a building chamber as a translated apartment chamber, apply the preceding
lemma, and use the assumed pointwise action of its normalizer element. This
proves membership in the existing pointwise fixer of the building chamber.
The normalizer premise is retained explicitly; this helper alone does not prove
the simply connected chamber stabilizer statement over the maximal unramified
field.
