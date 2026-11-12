# Axiom 4.1.1 under based group isomorphisms

Module `Langlands.Geometry.Building.FullValidity.DatumTransport.Realization`.

## Purpose and provenance

Internal infrastructure for `KPBuildingDatumTransportStatement`: KP Axiom 4.1.1 (the building
axiom of corrected Definition 4.1.26) for the source datum gives Axiom 4.1.1 for the
transported datum. The proof follows the Library's same-group comparison
`ValuationBuildingRealizationTransport`; the source does not state this transport.

## Contents

- `facetEquivOfIsBuildingIso`: a building isomorphism induces a bijection of facets.
- `PolysimplicialRealization.mapBuildingIso`: a polysimplicial realization carried along a
  building isomorphism (with its inverse also a building isomorphism), with lemmas that its
  apartments, building property, polysimplicial action (for an equivariant isomorphism) and
  face compatibility are preserved (`facetPrecedes_facetEquiv_iff_of_chart`).
- `image_apartmentImage_basedBuildingEquiv`: the standard apartment is sent onto the standard
  apartment.
- `innerIso_basedTransport`, `conjTorus_basedTransport`, `conjTorus_basedTransport_eq_iff`:
  conjugation by `g` followed by `f` is `f` followed by conjugation by `f(g)`, so conjugate
  tori correspond.
- `HasTorusApartmentCorrespondence.basedTransport`,
  `HasNormalizerApartmentStabilizer.basedTransport`.
- `PolysimplicialRealization.basedTransport` and `SatisfiesBuildingAxiom.basedTransport`.
