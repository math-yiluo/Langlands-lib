# Pointwise facet stabilizers

This internal application of the existing root geometry and Tits-system
correspondence proves that a setwise facet stabilizer in the actual zero
subgroup fixes the facet pointwise. It works on the supplied quotient and
original action at every universe parameter, including rank zero. It does
not construct the global building distance.

The generic `eqOn_facetClosure_of_torsor_face_fixing` chooses affine
coordinates on a real affine torsor with finite dimensional normed translation
space. Transport preserves the existing rank-zero-compatible affine root
axioms. The compactness theorem in `AffineFacetCompactness` and convexity of
the weak-sign facet closure supply the premises of the vertex-generation
criterion in `AffineFacetVertexGeneration`. Conjugating the affine map into
these coordinates therefore shows that stabilization of every incident facet
implies pointwise fixation of the entire facet closure.

`apartmentBuildingFacet p` is the image of the existing root facet of `p`
under the original apartment chart. Its incidence lemma uses the same base
chart in the existing definition of `FacetPrecedes`. Under the original
apartment axioms, compatible apartment facets and `IsBuildingTitsSystem`,
`normalizer_eqOn_facetClosure` applies the reversed incidence/stabilizer
correspondence to every incident face. A normalizer element in the zero
subgroup stabilizing the chosen facet thus stabilizes each such face.
Chart injectivity translates this into the affine face-fixing criterion.

`facetZeroStabilizer_smul_apartmentMap` also assumes the original normalizer
apartment-stabilizer equality. For an element `k` of the zero subgroup
stabilizing a base facet, the existing sharp-fixer apartment transport supplies
`r` fixing the whole facet pointwise and sending `k` times the base apartment
back to the base apartment. The root-cover inclusion places this sharp fixer
inside the actual simply connected image, hence inside the zero subgroup.
The product `r*k` is then a zero-subgroup normalizer element stabilizing the
facet. Its pointwise fixation, followed by cancellation of `r`, proves the
claim for `k`.

For arbitrary facets, `exists_zero_smul_apartmentImage` derives apartment
transitivity within the zero subgroup from the actual Tits-system
correspondence. If `a` and `b` represent an apartment and the base apartment
as restricted apartments, `b*a⁻¹` conjugates their contained facet stabilizers.
The existing injectivity result recovers equality of the actual apartments.
In particular, no distinguished-base identification with the restricted
apartment of the identity is assumed.

Finally, `facetZeroStabilizer_smul_eq` moves a containing apartment to the base
by such a zero-subgroup element `t`. Compatible apartment facets identify the
translated facet as an apartment facet. The element `t*k*t⁻¹` remains in the
zero subgroup and stabilizes that facet, so the base-facet result applies.
Cancellation of `t` proves pointwise fixation of the original facet.
No normality of the zero subgroup in the ambient rational-point group is
assumed. These are independently derived consequences of existing Library
interfaces, with no new literature assertion or geometric premise.
