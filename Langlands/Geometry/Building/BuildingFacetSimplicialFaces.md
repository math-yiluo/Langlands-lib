# Original quotient simplex faces under actual-vertex independence

This derived construction uses the original valuation quotient and its
original vertices and facets. Apartment axioms, injectivity of the original
apartment map and affine independence of every entire actual apartment-facet
vertex family are explicit hypotheses. The global realization additionally
assumes the full actual `IsBuildingTitsSystem` comparison. The building theorem
also assumes admissibility of every singleton simple type. None of these
hypotheses is proved here.

`apartmentVertexEmbedding` restricts an injective original chart to the original
vertex types. `buildingFacetVertexSet_eq_image` identifies every original
facet's entire vertex set in any original chart presentation. Given a nonempty
subset of these vertices, pull it back along that embedding. The torsor simplex
criterion realizes this pullback as the entire vertex set of an original
apartment facet. Its image is an original quotient facet with exactly the
prescribed vertices. Finiteness and nonemptiness come from the existing actual
quotient vertex theorems. Thus `buildingFacetVertexSimplicialComplex` has faces
exactly the entire vertex sets of the original quotient facets.

For any supplied face-compatible realization, `apartmentClosedFacetOrderIso`
matches the realized complex facets inside an original apartment `g • A` with
the original closed apartment facets. A closed facet is sent to the realized
preimage of its chart image. Order agreement combines face compatibility, the
existing chart incidence criterion and the closed-facet face criterion.
Surjectivity uses the existing presentation of every facet contained in `g • A`.
Closed facets determine open facets, so the chosen representative is
irrelevant. `isPolysimplicial_apartmentComplex_of_affineIndependent` transfers
the torsor polysimplicial theorem along this isomorphism to every original
apartment complex.

Under the full actual Tits comparison, the existing global vertex-finset
incidence theorem identifies inclusion of these vertex sets with the original
facet incidence. This constructs `buildingFacetSimplicialOrderIso` and the
one-factor `buildingFacetPolysimplicialOrderIso`. Inverting the latter gives
`buildingFacetSimplicialRealization` on the original quotient facets, with exact
face compatibility. The existing coordinate-fiber criterion makes its canonical
original rational-point action polysimplicial: for a singleton factor index,
agreement on one coordinate is equality of product vertices. With singleton
admissibility, `buildingFacetSimplicialRealization_isBuilding` applies the
existing Tits realization building theorem, using the apartment theorem above.

All results are internal consequences of the imported transport, simplex,
actual-vertex incidence, original-action and Tits-realization APIs. No new
literature assertion is used. This does not prove apartment-vertex independence
for actual irreducible factors, a product decomposition, the supplied Tits
comparison, admissibility, the building apartment axioms, the torus and
normalizer clauses, or the unconditional construction statement.

Integration uses module-specific names for local instances. Their types, values,
and local instance scopes are unchanged.
