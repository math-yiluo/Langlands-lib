# Topology of adelic points, given the covering by levels

Author: Worker 105.

This module proves the topological part of Conrad's p.17 claims on adelic points, for both
kinds of global field. The source is Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (2011), printed p.17. The claims are local compactness, the Hausdorff property and
second countability, in the third conjunct of `NumberFieldSpaceAdelePointsStatement` and
`CurvePlaceSpaceAdelePointsStatement`. They are derived from the assumption that every adelic
point comes from a level.

## Declarations

Namespace `Langlands.Global.AdelicSpacePointsProof`.

- `numberField_stageMap_transition`, `curve_stageMap_transition`: the stage maps are compatible
  with the changes of stage.
- `numberField_stage_locallyCompact_t2`, `curve_stage_locallyCompact_t2`: every stage is locally
  compact and Hausdorff. It is homeomorphic to a level of the base change, which has these
  properties by `AdelicSpaceLevelTopologyProof.numberField_locallyCompact_t2` (resp.
  `curve_locallyCompact_t2`).
- `numberField_points_of_cover`, `curve_points_of_cover`: suppose every adelic point comes from a
  level. Then the adelic points are locally compact, Hausdorff and second countable.
  - The inputs are: the stages are open embeddings (`AdelicSpacePointStagesProof`); they are
    locally compact, Hausdorff and second countable (`AdelicSpaceLevelSecondCountable`); and
    there are countably many of them.
  - Any two adelic points lie in a common stage because the stages are directed.
  - The `FinalStage` cover lemmas then apply.
