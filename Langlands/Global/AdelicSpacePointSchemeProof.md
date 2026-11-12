# Adelic points of schemes viewed as algebraic spaces

Author: Worker 105.

This module proves the scheme comparison clauses of Conrad's p.17 claims. The source is
Brian Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed p.17: "...
recovering our earlier topological constructions" for schemes. The clauses are
`Langlands.Global.NumberFieldSpaceAdelePointSchemeStatement` and
`Langlands.Global.CurvePlaceSpaceAdelePointSchemeStatement`. Let `U` be a scheme over the
`S`-integers of a global field that is locally of finite type, quasi-compact and separated. Then
`schemeRingPointsEquiv` is a homeomorphism between two spaces:
- the adelic points of the associated algebraic space, with `numberFieldSpaceAdelePointTopology`
  (resp. `curvePlaceSpaceAdelePointTopology`);
- the adelic points of `U`, with the published fixed-model topology
  `numberFieldFixedModelAdelePointTopology` (resp. `curvePlaceFixedModelAdelePointTopology`).

The proof uses neither quasi-compactness nor the limit comparison of points: both topologies are
final for the same stages.

## Declarations

Namespace `Langlands.Global.AdelicSpacePointSchemeProof`.

- `baseChange_instances`: base change keeps local finite type and separatedness of schemes.
- `numberField_factor`, `curve_factor`: every factor of a level gives a homeomorphism
  (`SchemeSpacePointComparison.isHomeomorph_localFactor`). The factors are of two kinds:
  - completions, through the identity;
  - completed valuation rings, through the inclusion into the completion, which is an open
    embedding.

  Each factor carries the normed-field and henselian structures of `AdelicSpaceLocalFields`. The
  factors are reduced (`numberFieldLevelFactor_isReduced`, `curvePlaceLevelFactor_isReduced`),
  and their units are open (`adelicLocalFactorUnits`).
- `numberField_level`, `curve_level`: on a level, `numberFieldSpaceLevelTopology` of the space of a
  scheme corresponds to `numberFieldLevelModelPointTopology` (resp. the curve-place versions), by
  `SchemeSpacePointComparison.isHomeomorph_coordinate`.
- `numberField_stage`, `curve_stage`: on the stage of a level `T ⊇ S`, the two topologies
  correspond. Each is induced from the level topology of a base change to the `T`-integers:
  - the space side from the base change of the space;
  - the scheme side from the base change of the scheme.

  These are identified by `baseChangeSchemeIso`, a homeomorphism for level topologies
  (`isHomeomorph_coordinate_iso`). The two point identifications then agree definitionally.
- `numberField_scheme`, `curve_scheme`: both global topologies are final for the stage maps
  `X(A_T) → X(𝔸)`, and `schemeRingPointsEquiv` commutes with them. So the stagewise homeomorphisms
  give a global one (`FinalStage.isHomeomorph_of_stages`).
- `numberFieldSpaceAdelePointScheme : NumberFieldSpaceAdelePointSchemeStatement.{u}` and
  `curvePlaceSpaceAdelePointScheme : CurvePlaceSpaceAdelePointSchemeStatement.{u}`: the clauses as
  stated. The function-field clause's hypothesis that `S` is nonempty is not used, and neither is
  quasi-compactness.
