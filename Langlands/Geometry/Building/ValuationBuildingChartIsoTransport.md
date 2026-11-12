# Chart isomorphisms from transports over one field

This is an internal coherence unit toward Kaletha–Prasad Axiom 4.1.17
(compatibility with isomorphisms) for the valuation-quotient buildings of
supplied `ValuationBuildingData`. It does not prove that axiom. It records that
the existing same-field identifications of apartment data are chart
isomorphisms in the sense of `KPApartmentData.IsChartIso`
(module `Langlands.Geometry.Building.ValuationBuildingChartIso`).

## Provenance

The source motivation is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Axiom 4.1.17, printed p.162 (PDF p.193), read with the authors'
corrections of 1 November 2024 (PDF p.27). Registered source IDs:
`kaletha-prasad-2023-bruhat-tits-new-approach`,
`kaletha-prasad-2024-corrections`. The declarations are derived from the
published API: `KPApartmentData.reindexOrder` and its apartment and building
identifications (`IntegerValuationLocalComparison`), the transport
`KPApartmentData.transport` with `transportEquiv` (`CrossTorusApartmentData`),
and the comparison with separately supplied data
`reducedBuildingTransportEquivOfMem`, `apartmentTransportAffineEquivOfMem`,
`transported_affineRoots_of_mem` and `transport_eq_iff_exists_mem`
(`CrossTorusApartmentComparison`, `CrossTorusBuildingComparison`). They are not
statements from the source.

## Same torus

Here `D`, `E` are apartment data for one `i : S → G` over a field `k`.

- `exists_isChartIso_of_eq`: if `D = E`, there are an affine equivalence of
  apartments and an equivalence of reduced buildings forming a chart
  isomorphism along `MonoidHom.id` with base point `1`. The proof substitutes
  the equality and uses `IsChartIso.refl`.
- `isChartIso_reindexOrder`: for an equality `h : ω = ω'` of field orders,
  `D.reindexOrderBuilding h` is a chart isomorphism from `D` to
  `D.reindexOrder h` along the identity, with base point `1` and apartment map
  `D.reindexOrderApartment h`. The proof is `cases h` and `IsChartIso.refl`.

## Transport along torus and group isomorphisms

Here `e : S ≅ S'`, `f : G ≅ H` and `h : i ≫ f.hom = groupHom e.hom ≫ j`, with
`D` apartment data for `i` and `E` for `j` (same field order `ω`).

- `isChartIso_reducedBuildingTransportEquivOfMem`: if the transport of the
  family of one point `x₀` of `D` lies in `E`, the published comparison
  `D.reducedBuildingTransportEquivOfMem e f h E x₀ h₀` is a chart isomorphism
  along `rationalPoints.map f.hom`, with base point `1` and apartment map
  `D.apartmentTransportAffineEquivOfMem e f h E x₀ h₀`. The chart formula
  follows from `reducedBuildingTransportEquivOfMem_smul` and
  `reducedBuildingTransportEquivOfMem_apartmentMap`; the affine roots are
  `transported_affineRoots_of_mem`.
- `exists_isChartIso_of_transport_eq`: if `D.transport e f h = E`, some chart
  isomorphism from `D` to `E` along `rationalPoints.map f.hom` with base point
  `1` exists; the point `x₀` comes from `transport_eq_iff_exists_mem`.
- `transport_transport_symm`: transporting `E` along the inverse isomorphisms
  (square `torusTransport_inverse_square e f h`) and then along `e`, `f`
  recovers `E`; this is `apply_symm_apply` for `transportEquiv e f h`.
- `exists_isChartIso_transport_symm`: hence the reduced buildings of the
  inverse transport of `E` and of `E` are related by a chart isomorphism along
  `rationalPoints.map f.hom` with base point `1`.

No building axiom, V 7, AS 5 or availability hypothesis is used.
