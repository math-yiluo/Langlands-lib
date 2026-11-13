# Closed-facet coordinate changes and vertex-set invariance over any field

This internal prerequisite applies to `D : KPApartmentData i ω` over an
arbitrary field and at arbitrary universe `u`. Its one additional premise
is AS4: each extended affine root is an ordinary affine root or has its
double among the ordinary affine roots.

`exists_normalizer_eq_on_translated_facetClosure` extends a coordinate
change at one quotient point to the entire weak-sign closed facet of
that point. The original quotient relation gives a normalizer element
`n` and a sharp-fixer element `g⁻¹ n` at the point. The published
`sharpFixer_singleton_le_of_mem_facetClosure` puts this sharp-fixer element
in every point fixer of the closed facet. Multiplication by `g` gives
the asserted equality throughout that closed facet.

`facetClosureVertexImage g Ω` is the image, in the original reduced
quotient and translated by `g`, of every original apartment vertex in
the closure of a facet meeting `Ω`. It has no finiteness or nonemptiness
assumption.

`smul_mem_facetClosureVertexImage` proves that each element fixing every
point of the translated image of `Ω` preserves this vertex image.
For a vertex in the closed facet of `p ∈ Ω`, apply the preceding
coordinate-change theorem to `g⁻¹ h g`, which fixes the image of `p`.
The resulting normalizer element fixes `p`. Its unconditional
root-preserving action preserves the closed facet and the singleton
facet defining a vertex. Its action on the chosen vertex agrees in the
quotient with that of `g⁻¹ h g`, giving the required membership.

The construction and proofs are derived from the published quotient
relation, the generic AS4 sharp-fixer comparison in
`BuildingFacetIncidence`, and the unconditional normalizer root action
in `NormalizerAffineRootAction`. The first proof generalizes the
existing local-field coordinate-change theorem from
`BuildingFacetIncidence`; its argument uses no local-field property.
No building metric, affine-root-system predicate, apartment injectivity,
or integral model is assumed. This module supplies invariance only;
finiteness and containment of vertex-fixer intersections remain
separate obligations.
