# Topology on adelic points of algebraic spaces

Author: Worker 105.

This module constructs the topology that Brian Conrad, *Weil and Grothendieck approaches to
adelic points* (December 31, 2011), puts on the adelic points of algebraic spaces on printed
p.17, for global fields of both characteristics. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module contains
definitions only and asserts no properties.

Conrad writes on printed p.17: "Since Theorem 3.4 is valid for algebraic spaces, the natural
map `lim_{S'} X_S(A_{F,S'}) → X_S(A_F)` is bijective for any separated algebraic space `X_S`
of finite type over `O_{F,S}` (where `S'` varies through the finite sets of places containing
`S`). Thus, exactly as in the scheme case, we can functorially topologize `X(A_F)` for any
separated algebraic space `X` of finite type over `F`."

## Definitions

All constructions are made for both global field types, with the same names except for the
prefix: `curvePlace` for a function field `F` over a field `k`, with places
`AlgebraicCurve.Place k F` and `S`-integers `curvePlaceSIntegers k F S`; `numberField` for a
number field `K`, with a finite set `S` of finite places and Mathlib's `S`-integers. Let `X`
be an algebraic space over the spectrum of the `S`-integers (from
`Langlands/AlgebraicGeometry/AlgebraicSpace/Basic.lean`).

- `RingPoints.mapEquiv e`: an isomorphism `e : X ≅ Y` of algebraic spaces identifies their
  `A`-valued points, by `RingPoints.map e.hom` with inverse `RingPoints.map e.inv`.
- `curvePlaceSpaceStageEquiv`, `numberFieldSpaceStageEquiv`: for a finite set `T ⊇ S`
  (`AdelicLevelIndexAbove S`), the points of `X` with values in the level `A_{F,T}`, viewed
  as an algebra over the `S`-integers (`curvePlaceAdeleLevelOver`,
  `numberFieldAdeleLevelOver`), are the `A_{F,T}`-points of the base change of `X` to the
  `T`-integers (`curvePlaceSpaceLevelBaseChange`, `numberFieldSpaceLevelBaseChange`). This is
  the published base-change identification `baseChangeRingPointsEquiv`.
- `curvePlaceSpaceStageTopology`, `numberFieldSpaceStageTopology`: the topology on these
  stage points is induced along the stage equivalence from the published level topology
  `curvePlaceSpaceLevelTopology` / `numberFieldSpaceLevelTopology` of the base change. That
  topology is induced from the product of the local point topologies, through the
  bijection of Conrad's Proposition 5.2 (`Langlands/Global/AdelicSpaceLevelTopology.lean`).
- `CurvePlaceSpaceAdelePoints`, `NumberFieldSpaceAdelePoints`: the points of `X` with values
  in the full adele ring, viewed as an algebra over the `S`-integers (`curvePlaceAdeleOver`,
  `numberFieldAdeleOver`). For number fields this is Mathlib's `Adeles K`, including every
  infinite factor.
- `curvePlaceSpaceStageMap`, `numberFieldSpaceStageMap`: change of coefficients along the
  inclusion of the level `A_{F,T}` in the full adele ring.
- `curvePlaceSpaceAdelePointTopology`, `numberFieldSpaceAdelePointTopology`: the topology on
  the full adelic points of `X` is the final topology for all stage maps,
  `⨆ T, coinduced (stage map T) (stage topology T)`.
- `curvePlaceSpaceGenericFiber`, `numberFieldSpaceGenericFiber`: the generic fibre of `X`,
  its base change along the spectrum of the inclusion of the `S`-integers in the field.
- `CurvePlaceSpaceFieldAdelePoints`, `NumberFieldSpaceFieldAdelePoints`: the adelic points of
  an algebraic space `Y` over the field, with the full adele ring as an algebra over the
  field.
- `curvePlaceSpaceGenericFiberEquiv`, `numberFieldSpaceGenericFiberEquiv`: the adelic points
  of `X` are the adelic points of its generic fibre (`baseChangeRingPointsEquiv`), which is
  Conrad's identification (3.5.1) for algebraic spaces.
- `curvePlaceSpaceSpreadEquiv`, `numberFieldSpaceSpreadEquiv`: given an isomorphism `e` from
  the generic fibre of `X` to an algebraic space `Y` over the field, the adelic points of `X`
  are identified with those of `Y`.
- `curvePlaceSpaceSpreadTopology`, `numberFieldSpaceSpreadTopology`: the topology on `Y(A_F)`
  attached to the spread `(S, X, e)`. It is induced from the full adelic point topology of
  `X` along the inverse of the spread identification.

The function-field generic fibre identification uses a perfect constant field, a function
field `FunctionField k F` and the compatible `RatFunc k`-algebra structure. These are the
hypotheses of the published diagonal `curvePlaceAdeleLevelDiagonal_eq`, used for the
compatibility of the scalar actions. The other function-field constructions need only fields
`k` and `F` with a `k`-algebra structure.

## Relation to the source and derived content

Conrad topologizes the colimit `lim_{S'} X_S(A_{F,S'})` and transports the topology along the
bijection with `X_S(A_F)`. Here the topology is defined directly on `X_S(A_F)` as the final
topology for the stage maps. When the map from the colimit is bijective, this is the
transported colimit topology. Bijectivity for separated spaces of finite type (Conrad's
appeal to Theorem 3.4) is not asserted here. The published scheme case
(`Langlands/Global/AdelicFixedModelCocone.lean`) uses the same construction.

Conrad's topology on `X(A_F)` for an algebraic space `X` over the field is defined through a
model over some ring of `S`-integers. Here the model and the generic-fibre isomorphism are
explicit data. The topology is indexed by them, as in the published scheme case
(`Langlands/Global/AdelicGenericFiberPoints.lean`). Independence of the model, existence of
models, and Conrad's claims that the topology is locally compact, Hausdorff, second countable,
functorial and compatible with fibre products and closed immersions are separate statements.

Also derived here: the names, the packaging over the `S`-integers through
`curvePlaceAdeleLevelOver` and `numberFieldAdeleLevelOver`, and the generality (no
separatedness or finiteness hypotheses in the definitions; `S` may be empty).
