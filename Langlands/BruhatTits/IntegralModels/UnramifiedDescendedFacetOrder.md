# Reverse incidence from descended facet images

This is internal derived content. It composes the published full-facet lift
and its incidence reflection with global unramified zero-fixer recovery and
the actual special-fibre image comparison. It makes no new translation of
original literature.

The geometric data are a valuation building `B` over a local field, an
unramified zero datum `E`, and supplied maximal-unramified building data `C`
for an affine group `H`. The group `H` need not be presented as a base change
of the downstairs group. A rational-point homomorphism `ρ`, a quotient point
map `e`, and an affine apartment map `a` satisfy equivariance, compatibility on
the canonical apartment, and exact pullback of its affine facets. Downstairs
apartment axioms and common apartments are explicit. All declarations hold at
arbitrary universe `u`.

`facetPrecedes_of_descendedZeroFixer_le` proves that containment of
`E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val)` in the corresponding subgroup
for `Fd` implies `Fd ≺ Fc` in the original downstairs building. Each full
downstairs facet has nonempty image contained in its full upstairs
`facetLift`. Global zero-fixer containment therefore gives reverse incidence
of those upstairs full facets. The published `facetPrecedes_facetLift_iff`
reflects it downstairs. Neither image is required to be an entire upstairs
facet; neither injectivity nor surjectivity of `e` is needed.

`HasDescendedFacetZeroFixerOrderReflection` is the proposition that this
actual zero-fixer assignment reflects reverse incidence for every pair of
downstairs full facets. It depends only on `B`, `E`, `C` and `e`; it does not
assume the apartment hypotheses in its definition.
`hasDescendedFacetZeroFixerOrderReflection` proves it from the displayed
apartment and building hypotheses by applying the preceding theorem.

`facetPrecedes_of_unramifiedSpecialFibreImage_le` treats two actual relative
component model morphisms with common target over a Henselian domain `R`
whose fraction field is the maximal unramified field and whose residue field
is algebraically closed. Each source neutral integral-point subgroup is
explicitly characterized by the zero fixer of the corresponding downstairs
facet image. Each contains the target neutral congruence subgroup.
Containment of the two actual schematic-image subgroup functors, on all
residue-scheme tests, then implies reverse downstairs incidence. The proof
uses `specialFibreImage_le_iff_integralPoints_le` and rewrites the two source
characterizations before applying the geometric theorem.

The result concerns the actual special-fibre images over the displayed
upstairs ring. It does not prove the congruence containments, transport
downstairs residue images to these images, compare reductive quotient images,
or establish parabolicity or attainment of all parabolics. The host
`UnramifiedFacetParabolicOrderStatement` remains a separate proof obligation.
