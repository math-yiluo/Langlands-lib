# Enlarging the initial set of a spread

Author: Worker 105.

This module is a helper for the spread clauses of Conrad's p.17 claims on adelic points of
separated algebraic spaces. The claims are `NumberFieldSpaceSpreadStatement` and
`CurvePlaceSpaceSpreadStatement` in `Langlands.Global.AdelicSpacePointTopologyStatement`. The
source is Brian Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.17, which says the topology on adelic points does not depend on the model.

The module proves one step of that independence: enlarging the finite set of places of a model.
- Let `X` be a separated model of finite type over the `S`-integers, and `S ⊆ V`.
- Then the base change `X_V` of `X` to the `V`-integers gives the same topology on adelic
  points. Its generic fibre is identified with that of `X` by the iterated base change
  isomorphism.

## Declarations

Namespace `Langlands.Global.AdelicSpaceSpreadInitialSet`. Both kinds of global field are
covered; the global function field versions carry the prefix `curve` and need `S.Nonempty` where
the stage transitions do.

- `numberFieldLift`: a level above `V` viewed as a level above `S`.
- `numberFieldGenericFiberIso`: the generic fibre of `X_V` is the generic fibre of `X`
  (`BaseChangeComparison.compIso`).
- `numberFieldStageEquiv`, `numberFieldPointsEquiv`: the points of `X_V` at a level `T ⊇ V`, and
  its adelic points, are the corresponding points of `X` (`baseChangeRingPointsEquiv`).
- `numberFieldTowerIso`: the iterated base change `(X_V)_T ≅ X_T`.
- `numberField_stage_comm`: under the stage identifications, `numberFieldStageEquiv` is the
  tower isomorphism (`baseChangeRingPointsEquiv_towerIso`).
- `numberField_points_comm`: the stage maps commute with the identifications.
- `numberField_stage_isHomeomorph`: the identification of stages is a homeomorphism. It
  composes three homeomorphisms:
  - the stage identification of `X_V` (`numberField_stageEquiv_isHomeomorph`);
  - the tower isomorphism on level topologies (`isHomeomorph_coordinate_iso`);
  - the inverse stage identification of `X`.
- `numberField_pointsEquiv_isHomeomorph`: the identification of adelic points is a
  homeomorphism for the final topologies, assuming `X` is separated of finite type.
  - Continuity is checked on the stages `T ⊇ V`.
  - Continuity of the inverse is checked on a stage `T ⊇ S`, which maps into the stage
    `T ∪ V` by an open embedding (`numberField_stage_transition`).
- `numberField_genericFiber_comm`, `numberField_spreadEquiv_comm`: the identification is
  compatible with the generic fibres and the spread identifications.
- `numberField_spreadTopology_eq` and `curve_spreadTopology_eq`: **enlarging the initial set**.
  For a separated `X` of finite type over the `S`-integers, `S ⊆ V`, and
  `e : numberFieldSpaceGenericFiber K S X ≅ Y`:

  `numberFieldSpaceSpreadTopology K S X Y e = numberFieldSpaceSpreadTopology K V X_V Y (numberFieldGenericFiberIso K hSV X ≪≫ e)`,

  where `X_V = numberFieldSpaceLevelBaseChange K hSV X`. The curve version is the same with
  `hS : S.Nonempty`.
