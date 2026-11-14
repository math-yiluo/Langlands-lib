# Full facets under a restricted apartment map

This is an internal consequence of the published facet partition and apartment
injection results. It formalizes the geometric restriction step needed when a
building over a local field is embedded in the maximal unramified building.
It introduces no new literature translation.

Let `B` be the existing valuation building data over a nonarchimedean local
field and let `C` be integer-valued building data over any field. A homomorphism
`ρ` of the actual rational-point groups, a map `e` of their original quotient
point carriers, and an affine apartment map `a` are supplied. The hypotheses are:

- `B.SatisfiesApartmentAxioms`;
- every two downstairs quotient points lie in a common actual apartment;
- `e` is equivariant for `ρ` and agrees with `a` on the displayed apartment;
- for every apartment point `x`, the inverse image under `a` of the upstairs
  full affine-root facet through `a x` is exactly the downstairs full affine-root
  facet through `x`.

No surjectivity or injectivity of the supplied point map is assumed. The upstairs
data carry connected reductivity and maximal splitness, which give their
published apartment injection and full-facet partition.

`map_translatedApartmentMap` combines equivariance and apartment compatibility.
`map_mem_buildingFacetAt_iff` puts two downstairs points in a common apartment.
The containing facets in both quotients have their published descriptions as
translated affine-root facet images. Upstairs apartment injection identifies the
coordinates of any witness of upstairs membership. The exact restricted-facet
identity then reflects membership downstairs. Conversely, a witness of
downstairs membership maps to an upstairs witness by equivariance and that same
identity. This proves equivalence of membership in the containing full facets.
`mapped_buildingFacetAt_eq_iff` is the corresponding equality criterion.

`facetRestrictionEmbedding` is an actual function embedding from full downstairs
building facets to full upstairs building facets. Its function chooses a point
of the nonempty downstairs facet and takes the upstairs facet containing its
image. The equality criterion and downstairs partition prove injectivity.
`preimage_facetRestrictionEmbedding` states that the complete inverse image of
this upstairs facet is the original downstairs facet. Consequently,
`image_subset_facetRestrictionEmbedding` puts the image of every downstairs
facet in its assigned upstairs facet. The final application theorem identifies
the embedding on the facet containing any given downstairs point.

These results concern full facets as subsets of the original quotients, at
arbitrary universe `u`. They assert neither an incidence comparison nor a
parabolic classification, and do not prove the host unramified parabolic order
statement.
