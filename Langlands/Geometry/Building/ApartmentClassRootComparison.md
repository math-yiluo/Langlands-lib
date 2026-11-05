# Actual affine roots for equal valuation classes

This internal comparison extends the Library's
`apartmentAffineEquivOfCarrierEq` from `CrossTorusApartmentComparison`.
For two `KPApartmentData i ω` with equal carrier sets, that affine
equivalence sends a point to the very same valuation family, with its
membership proof in the second class. It has identity derivative on
`TranslationSpace i` and intertwines the original normalizer actions.
Neither local-field hypotheses nor an apartment axiom is required here.
The valuation-family and derivative lemmas are reused from
`ConjugateApartmentIndependence` and registered here for simplification.

The results are direct consequences of the existing definitions. The
comparison retains every valuation value, so the actual filtration
subgroups at corresponding points and equal real levels are equal.
Inverse precomposition of a functional then identifies the affine root
groups, which are the intersections of these filtration groups over all
apartment points. Surjectivity of the affine equivalence proves both
directions. Inverse precomposition also preserves adding a positive
constant, so it identifies the strict affine root groups.

The functional derivative is unchanged because the affine comparison has
identity derivative. Hence both tests in the ordinary affine-root
definition agree: the derivative is the form of an actual relative root,
and the affine root subgroup is not contained in the product of the strict
affine root subgroup with the original double-root subgroup. This proves
membership equivalence for ordinary affine roots. Bijectivity of functional
transport upgrades membership equivalence to equality of the complete
transported root sets. The generic facet transport theorem then identifies
the full sign-defined facets.

The definitions `apartmentFacetEquivOfCarrierEq` and
`apartmentChamberEquivOfCarrierEq` use this complete root-set equality to
construct equivalences of the subtypes of all full apartment facets and all
apartment chambers. They specialize the equivalences in `AffineFacetTransport`.
Each forward map takes the image under the original
`apartmentAffineEquivOfCarrierEq`; the `_apply` lemmas record these formulas
by definitional equality. The inverse maps use the inverse point equivalence.

The premise is equality of the two valuation-class carriers. This module
does not prove uniqueness of omega-compatible classes, construct a
descended building, or identify such a building's roots with those of a
valuation class. It supplies the root and facet comparison once equality
of actual valuation classes has been established; it makes no assertion
of `SimplyConnectedFacetFixingStatement`.
