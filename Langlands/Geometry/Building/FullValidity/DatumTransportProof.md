# Proof of `KPBuildingDatumTransportStatement`

Module `Langlands.Geometry.Building.FullValidity.DatumTransportProof`.

## Statement proved

`KPBuildingDatumTransportStatement.{u}` (module
`Langlands.Geometry.Building.FullValidity.DatumTransportStatement`): for a full corrected KP
datum `D` on `G` satisfying the group axioms, an isomorphism `f : G ≅ H`, a commutative group
scheme `S` with `i : S → H` and an isomorphism `σ : S_D ≅ S` with `i_D ≫ f = σ ≫ i`, there is a full
datum `D'` on `H` satisfying the group axioms, with `D'.base.S = S` and inclusion `i`, and a
bijection `Φ : B(G) ≃ B(H)` of reduced buildings that is an equivariant isomorphism of buildings
along `rationalPoints.map f.hom` and whose inverse is an isomorphism of buildings.

## Provenance

The transport is derived from the data and the one-group clauses of KP Definition 4.1.26
(Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, Axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6,
4.1.8, 4.1.9, 4.1.16, 4.1.20 and 4.1.22, as corrected in the Library). The source does not
state it.

## Construction

`KPBuildingDatum.basedTransport D σ f h` keeps the abstract groups of `D` that do not live in
`G` (the centralizer `Z`, the integral model groups, special fibres, radicals and reductive
quotients) and composes every map into `G` (inclusions, generic identifications) with `f`,
and transports maps into or out of `S_D` along `σ`:

- `base := D.base.basedTransport σ f h` (module `DatumTransport.Building`): the valuation
  building data on `H` with torus `S` and inclusion `i`, apartment data transported by the
  Library's `KPApartmentData.transport`, centralizer and zero-subgroup data transported along
  `f` (module `DatumTransport.Base`);
- `realization` (module `DatumTransport.Realization`): the polysimplicial structure carried by
  the building isomorphism `basedBuildingEquiv`;
- `splitting` (module `DatumTransport.AffineApartment`): the derived and central tori of
  Axiom 4.1.4 with their maps composed with `f` and `σ`;
- `models` and `quotients`: the model family and the quotient family transported along the
  building transport package `BuildingTransportPackage.based` (modules
  `Langlands.BruhatTits.IntegralModels.Transport.*`), whose apartment map is
  `basedApartmentEquiv` and whose building map is `basedBuildingEquiv`;
- `rootDatum`: the root reflection data transported along `σ` and `f`
  (`RelativeRootReflectionData.transport`).

## Proof

`SatisfiesGroupAxioms.basedTransport` proves every field of `SatisfiesGroupAxioms` for the
transported datum from the same field for `D`:

- building (4.1.1): `SatisfiesBuildingAxiom.basedTransport`;
- bounded subgroups (4.1.2): `HasBoundedOpenStabilizers.basedTransport`;
- affine structure (4.1.4): `SatisfiesAffineApartmentAxiom.basedTransport`;
- affine root system (4.1.6): `HasRootReflections.basedTransport`,
  `SatisfiesApartmentAxioms.basedTransport`, `HasCompatibleApartmentFacets.basedTransport`;
- root group action (4.1.8): clause (1) holds for all data; clauses (2) and (3) by
  `HasZeroFixerGenerators.basedTransport` and `HasRootZeroFixers.basedTransport`;
- Tits system (4.1.9): `HasTitsSystem.basedTransport`;
- Iwahori decomposition (4.1.16): `HasIwahoriDecomposition.basedTransport` (module
  `DatumTransport.Iwahori`);
- Bruhat–Tits group schemes (4.1.20): `BuildingModelFamily.satisfiesModelAxioms_basedTransport`;
- reductive quotients (4.1.22):
  `BuildingModelQuotientFamily.satisfiesMorphismAxioms_basedTransport`.

The final theorem `kpBuildingDatumTransportStatement` takes `D' = D.basedTransport σ f h`;
`D'.base.S = S` and the equality of inclusions hold by definition (`rfl` and `HEq.rfl`), and
`Φ = basedBuildingEquiv` with `isEquivariantBuildingIso_basedBuildingEquiv` and
`isBuildingIso_basedBuildingEquiv_symm`. No hypothesis beyond those of the statement is used:
no assignment, availability or rebasing target is assumed.
