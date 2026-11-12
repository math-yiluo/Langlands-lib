# Axiom 4.1.6 under based group isomorphisms

Module `Langlands.Geometry.Building.FullValidity.DatumTransport.RootSystem`.

## Purpose and provenance

Internal infrastructure for `KPBuildingDatumTransportStatement`: KP Axiom 4.1.6 (AS 1, the
apartment axioms V 7 and AS 2–AS 5, and AS 6) for the source datum gives the same clauses for
the transported datum. The proofs follow the Library's same-group comparison modules
`ValuationBuildingRootReflectionTransport`, `ValuationBuildingApartmentAxiomTransport` and
`ValuationBuildingAxiomTransport`; the source does not state this transport.

## Contents

- `DatumTransport.isOppositeFactorPair_transport_iff`: opposite factor pairs `(u', u'')` for
  `(a, u)` correspond to pairs for `(σ(a), f(u))` under `f`.
- `DatumTransport.isTopologyCompatible_transport`: V 7 for a valuation family gives V 7 for the
  transported family. `f` and `f⁻¹` are continuous on rational points, so they restrict to a
  homeomorphism of root groups that matches the filtrations; bounded filtration pieces map to
  bounded sets.
- `ValuationBuildingData.HasCompatibleApartmentFacets.of_buildingIso`: AS 6 is carried along a
  building isomorphism `Φ` between data for possibly different groups, provided `Φ` is
  compatible with an affine apartment comparison `A` that matches the affine roots. This is the
  cross-group version of the Library's same-group lemma.
- `basedApartmentEquiv_val`, `basedApartmentEquiv_value`: the transported apartment point is the
  transported valuation family, and its values at `(σ(a), f(g))` are unchanged.
- `transportedRoots_extendedAffineRoots_basedApartmentEquiv`: the extended affine roots `Ψ′`
  correspond under the apartment comparison.
- `derivativeTransport_range_rootForm_basedApartmentEquiv`: the linear part of the comparison
  carries the root forms onto the root forms.
- `affineConjugation_normalizerAction_basedTransport`,
  `map_normalizerAction_range_basedTransport`: conjugation by the comparison carries the action
  of `n` to that of `f(n)`, so it carries the image of `N(F)` onto the image of `N_H(F)`.
- `HasRootReflections.basedTransport` (AS 1), `SatisfiesApartmentAxioms.basedTransport`
  (V 7 and AS 2–AS 5; simple connectivity, quasi-splitness and adjointness transfer along `f`)
  and `HasCompatibleApartmentFacets.basedTransport` (AS 6).
