# Facets under an affine comparison of root arrangements

This is an internal consequence of the Library's existing `facetRel`, `facet`,
`IsFacet`, `facetClosure` and `IsChamber` definitions and the actual
`affineFunctionalTransport` in `AffineWeylTransport`. No external theorem is
asserted and no affine root system or building axioms are assumed. The source
and target point and vector spaces may lie in independent universes.

For an affine equivalence `e : A ≃ᵃ[ℝ] B`, the root set is transported by inverse
precomposition: the value of the transported root at `e x` is the original
root's value at `x`. Thus the signs of all roots at two points agree on one
side exactly when they agree on the other side. This proves
`facetRel_transportedRoots_iff`.

`hyperplane_affineFunctionalTransport` identifies the zero hyperplane of a
transported functional with the affine image of its original zero hyperplane.
This is the existing theorem from `ValuationBuildingIsoGeometry`, relocated
here with the same name, hypotheses and proof for shared use by that module
and `AffineChamberCartanMarks`.

`image_facet_transportedRoots` identifies the full equivalence classes. In the
reverse inclusion the preimage point is `e.symm y`; this ensures equality of
whole facets, not merely containment. Injectivity of the image operation then
proves `isFacet_image_transportedRoots_iff`. The version
`isFacet_image_iff_of_transportedRoots_eq` rewrites an explicitly supplied
root-set comparison into the precise equivalence of the existing facet
predicates.

The same substitution in the weak sign condition identifies facet closures.
Finally, the characterization of chambers as full facets of points with all
root values nonzero proves `isChamber_image_transportedRoots_iff`.

The definitions `facetEquivOfTransportedRootsEq` and
`chamberEquivOfTransportedRootsEq` construct equivalences between the subtypes
of all full facets and all chambers, respectively, for two explicitly identified
root sets. They restrict the equivalence on sets induced by `e`, using the
proved facet and chamber predicate equivalences. Their forward maps take
images under `e`; their inverses take images under `e.symm`. The two `_apply`
lemmas record the forward maps by definitional equality.

These constructions and lemmas apply after an actual apartment and
root comparison has been established. In particular, they do not construct a
descended apartment, establish such a comparison for supplied valuation data,
or prove `SimplyConnectedFacetFixingStatement` or any instance of AS 5.
