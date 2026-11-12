# Point topologies of schemes viewed as algebraic spaces

Author: Worker 105.

Helper module for the proof of Conrad's p.17 claim that the topology on adelic points of
algebraic spaces recovers the scheme case
(`Langlands.Global.AdelicSpacePointTopologyStatement`). For a scheme `U` over a ring `C`, the
points of the associated algebraic space `(schemeToSpace _).obj U` carry the topologies of
`Langlands.Global.AdelicSpaceLevelTopology`, and the points of `U` carry the scheme point topology
`schemePointTopology`. This module compares the two. The points are identified by
`schemeRingPointsEquiv`.

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeSpacePointComparison`.

Base change, for a tower `C → D → A`:
- `baseChangeRingPointsEquiv_scheme`: the point identification of the base change of the space of
  `U` (`baseChangeRingPointsEquiv`) agrees with the scheme base change identification
  (`ringPointBaseChangeEquiv`) through `baseChangeSchemeIso`. Both are built from the same
  pullback adjunction, so the identity holds by `rfl`.
- `ringPointBaseChangeEquiv_scheme`: the same identity, solved for the scheme side.
- `schemeRingPointsEquiv_changeRing`: the identification commutes with change of coefficients
  (`rfl`).
- `isHomeomorph_of_eq_induced`: an equivalence is a homeomorphism when the source topology is
  induced from the target.

Factors, for a nontrivially normed field `L` that is a henselian valued field
(`IsHenselianValuedField`):
- `fieldValuedPointMap_id_scheme`: on `L`-points, the field-valued point map of the space of `U` is
  the composite of three maps:
  - the scheme base change to `L`;
  - the identification of the `L`-points of `U_L` with the points of its space;
  - the isomorphism `baseChangeSchemeIso`.
- `isHomeomorph_field`: let `U` be quasi-separated and locally of finite type. Then the
  field-valued topology on the `L`-points of its space is the scheme topology on `U(L)`. Each of
  the three maps is a homeomorphism:
  - scheme base change, by `schemeBaseChangeTopology_proof`;
  - étale-chart topology equals scheme topology on schemes, by
    `isHomeomorph_schemeRingPointsEquiv`;
  - isomorphisms of spaces, by `isHomeomorph_ringPointsMap_of_iso`.
- `isHomeomorph_factor`: let `R` be a reduced local topological ring with open units, and
  `φ : R → L` an open embedding. Let `U` be separated and locally of finite type. Then the
  field-valued topology along `φ` on the `R`-points of the space of `U` is the scheme topology on
  `U(R)`. The map `U(R) → U(L)` is continuous, open and injective
  (`schemeCoefficientContinuity_proof`, `schemeCoefficientOpen_proof`,
  `schemeSeparatedCoefficientInjectivity_proof`), so it is inducing, and the field case applies.
- `isHomeomorph_localFactor`: the same, followed by the scheme base change of `U` to `R`.

Coordinates, for families `π i : A → R i` and `φ i : R i → L i`:
- `localModelMap`: `U(A) → ∏ᵢ U_{Rᵢ}(Rᵢ)`, restriction to each factor followed by base change.
- `localModelProductTopology`: the product of the scheme topologies of the local models.
- `isHomeomorph_coordinate`: suppose every factor comparison is a homeomorphism. Then
  `coordinatePointTopology` on the points of the space of `U` is the topology induced along
  `localModelMap`. The two coordinate maps correspond under a product of homeomorphisms
  (`IsEmbedding.piMap`).
- `isHomeomorph_coordinate_iso`: an isomorphism of algebraic spaces is a homeomorphism for
  coordinate topologies. On each factor, it corresponds to the base-changed isomorphism on
  rational points (`CoordinatePointMaps.fieldValuedPointMap_map`).
