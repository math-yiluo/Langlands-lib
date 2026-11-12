# Morphisms on adelic points of separated algebraic spaces

Author: Worker 105.

This module proves the first clause of Conrad's p.17 functoriality claims, for both kinds of
global field. The source is Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(2011), printed p.17. The clause is the first conjunct of
`Langlands.Global.NumberFieldSpaceAdelePointMapsStatement` and of
`Langlands.Global.CurvePlaceSpaceAdelePointMapsStatement`. Let `f : X → Y` be a morphism of
separated algebraic spaces of finite type over the `S`-integers. Then `X(𝔸) → Y(𝔸)` is
continuous, and it is a closed embedding when `f` is a closed immersion. For function fields
`S` is nonempty.

The second conjunct, compatibility with fibre products, is not proved here.

## Declarations

Namespace `Langlands.Global.AdelicSpacePointMapsProof`.

Levels (`T` a finite set of places, spaces over the `T`-integers):
- `numberField_factor_continuous`, `numberField_factor_closed`, `curve_factor_continuous`,
  `curve_factor_closed`: each factor of a level is one of two kinds:
  - a completion, through the identity;
  - a completed valuation ring, through its inclusion into the completion.

  Either way the factor gives a field-valued topology over a henselian valued field
  (`AdelicSpaceLocalFields`). The results of `CoordinatePointMaps` apply, and the inclusions
  are injective.
- `numberField_level_continuous`, `numberField_level_closed`, `curve_level_continuous`,
  `curve_level_closed`: the same on the level topologies. The closed-embedding results use
  Proposition 5.2 (`numberFieldSpaceLevelPoints`, `curvePlaceSpaceLevelPoints`, for nonempty
  `T` in the function-field case) for both `X` and `Y`.

Stages (`T ⊇ S`, spaces over the `S`-integers):
- `numberFieldLevelMap`, `curveLevelMap`: the base change of `f` to the `T`-integers.
- `numberField_stageEquiv_map`, `curve_stageEquiv_map`: the stage identification
  `X(A_T) ≃ X_T(A_T)` is natural (`baseChangeRingPointsEquiv_map`).
- `numberField_stageEquiv_isHomeomorph`, `curve_stageEquiv_isHomeomorph`: the stage topology
  is induced along this equivalence, so the equivalence is a homeomorphism.
- `numberField_stage_continuous`, `numberField_stage_closed`, `curve_stage_continuous`,
  `curve_stage_closed`: transport of the level results. Base change keeps separatedness, finite
  type and closed immersions.

Full adelic points:
- `numberField_levelι_injective`, `curve_levelι_injective`: the inclusion of a level into the
  adeles is injective.
- `numberField_continuous`, `curve_continuous`: **continuity**. The topology on `X(𝔸)` is final
  for the stage maps `X(A_T) → X(𝔸)`, so this follows from continuity on stages
  (`FinalStage.continuous_of_stages`).
- `numberField_closed`, `curve_closed`: **closed immersions give closed embeddings**, by
  `FinalStage.isClosedEmbedding_of_stages`:
  - `f` is injective on `X(𝔸)` (`ClosedImmersionPoints.map_injective`);
  - it is a closed embedding on every stage;
  - a point `y ∈ Y(A_T)` whose image in `Y(𝔸)` comes from `X(𝔸)` comes from `X(A_T)`, by
    `ClosedImmersionPoints.exists_changeRing_eq` applied to the injective map `A_T → 𝔸`.

  This argument does not need every adelic point to come from a level.
