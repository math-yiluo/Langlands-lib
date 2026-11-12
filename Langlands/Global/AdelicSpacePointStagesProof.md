# The stages of adelic points of separated algebraic spaces

Author: Worker 105.

This module proves the open-embedding clause of Conrad's p.17 claims for both kinds of global
field (`Langlands.Global.NumberFieldSpaceAdelePointsStatement`,
`Langlands.Global.CurvePlaceSpaceAdelePointsStatement`, second conjunct). The source is Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed p.17. Let `X` be a
separated algebraic space of finite type over the `S`-integers, with `S` nonempty for function
fields. Then every stage map `X(A_T) → X(𝔸)` is an open embedding for the stage topology and the
final topology on `X(𝔸)`.

## Declarations

Namespace `Langlands.Global.AdelicSpacePointStagesProof`.

- `isDirected_levelIndex`: the finite sets containing `S`, ordered by inclusion, are directed
  (by unions).
- `numberField_stage_transition`, `curve_stage_transition`: for `T ≤ T'`, change of coefficients
  `X(A_T) → X(A_T')` along the level inclusion is an open embedding of stage topologies.
  - Under the stage identifications (`numberFieldSpaceStageEquiv`), this map is a composite:
    - the change of level from `T` to `T'` of the base change `X_T` of `X` to the `T`-integers,
      which is an open embedding by the level theorem
      (`AdelicSpaceLevelTopologyProof.numberField_transition`, `curve_transition`) applied to
      `X_T`;
    - the iterated base change isomorphism `towerIso`, which is a homeomorphism
      (`SchemeSpacePointComparison.isHomeomorph_coordinate_iso`).
  - The commutation is checked on sections: both sides are pullbacks of the same point of `X`
    along morphisms of test schemes with the same underlying morphism.
- `numberField_stage_isOpenEmbedding`, `curve_stage_isOpenEmbedding`: **stages are open
  embeddings**, by `FinalStage.isOpenEmbedding_stage`. The stage maps are injective because
  `X` is separated and the levels are subrings of the adeles
  (`RelativeIntegralPoints.changeRing_injective`). They are compatible with the transitions by
  functoriality of change of coefficients.
