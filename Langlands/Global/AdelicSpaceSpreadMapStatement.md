# Proper and smooth maps of algebraic spaces on adelic points

Author: Worker 105.

This module states Proposition 5.8 and Theorem 5.9 of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed p.17, for global
fields of both characteristics. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module only
states the results and contains no proofs.

Conrad writes: "Proposition 5.8. Let `f : X → Y` be a proper map between separated
algebraic spaces locally of finite type over a global field `F`. The map
`X(A_F) → Y(A_F)` is topologically proper." and "Theorem 5.9. Let `f : X′ → X` be a
smooth surjective map between separated algebraic spaces of finite type over a global
field `F`. Assume that the fibers of `f` are geometrically connected. Then the map
`X′(A_F) → X(A_F)` is open."

## Objects

The global fields are those of the published `AdelicSpacePointTopology.lean`: a number
field `K` with finite sets `S`, `U` of finite places and Mathlib's rings of `S`-integers;
or a function field `F` over a finite field `k`, with the compatible `RatFunc k`-algebra
structure, a `FunctionField k F` instance, and nonempty finite sets `S`, `U` of places
(`AlgebraicCurve.Place k F`) with the rings `curvePlaceSIntegers k F S`. The algebraic
spaces are the Library's actual algebraic spaces (from
`Langlands/AlgebraicGeometry/AlgebraicSpace/Basic.lean`).

- `IsSeparated X` (from `RingPoints.lean`): the diagonal of `X` is a representable closed
  immersion.
- `FiniteTypeOverRing C X` (from `Langlands/Global/AdelicSpaceLevelPointsStatement.lean`):
  `X` has a surjective étale atlas by an actual scheme that is locally of finite type and
  quasi-compact over `Spec C`.
- `curvePlaceSpaceGenericFiber`, `numberFieldSpaceGenericFiber` (from
  `AdelicSpacePointTopology.lean`): the generic fibre of a model `X` over the
  `S`-integers. A model of an algebraic space `Y` over the field is a pair of `X` and an
  isomorphism `e` from its generic fibre to `Y`.
- `CurvePlaceSpaceFieldAdelePoints k F Y`, `NumberFieldSpaceFieldAdelePoints K Y`: the
  points of `Y` with values in the full adele ring (for number fields Mathlib's
  `Adeles K`, including all infinite factors). `RingPoints.map g` is the map induced by
  `g : Y ⟶ W`.
- `curvePlaceSpaceSpreadTopology k F S X Y e`, `numberFieldSpaceSpreadTopology K S X Y e`:
  Conrad's topology on `Y(A_F)` attached to the model `(S, X, e)`, described in
  `AdelicSpacePointTopology.md`.
- `IsProperMorphism g`, `IsSmoothMorphism g`, `IsSurjectiveMorphism g`,
  `HasGeometricallyConnectedFibres g` (from
  `Langlands/AlgebraicGeometry/AlgebraicSpace/SpaceMorphismProperties.lean`): proper,
  smooth and surjective morphisms of algebraic spaces and morphisms with geometrically
  connected fibres, following the Stacks Project as explained in
  `SpaceMorphismProperties.md`. None of them requires `g` to be representable.
- `IsProperMap` is Mathlib's proper map (continuous, and every cluster point of the image
  of a filter is the image of a cluster point of the filter; equivalently continuous and
  closed with compact fibres). `IsOpenMap` is Mathlib's open map.

## The statements

- `NumberFieldSpaceSpreadProperMapStatement`: let `K` be a number field, `S`, `U` finite
  sets of finite places, `X` and `Z` separated algebraic spaces of finite type over the
  `S`-integers and the `U`-integers, `Y` and `W` algebraic spaces over `Spec K` with
  isomorphisms `e`, `f` from the generic fibres of `X`, `Z`, and `g : Y ⟶ W` a morphism
  with `IsProperMorphism g`. Then `RingPoints.map g` is an `IsProperMap` from `Y(A_K)`
  with the topology attached to `(S, X, e)` to `W(A_K)` with the topology attached to
  `(U, Z, f)`.
- `NumberFieldSpaceSpreadSmoothOpenStatement`: the same data, with `IsSmoothMorphism g`,
  `IsSurjectiveMorphism g` and `HasGeometricallyConnectedFibres g` in place of properness.
  Then `RingPoints.map g` is an `IsOpenMap` for these topologies.
- `CurvePlaceSpaceSpreadProperMapStatement`, `CurvePlaceSpaceSpreadSmoothOpenStatement`:
  the same for a function field `F` over a finite field `k`, with nonempty finite sets
  `S`, `U` of places.
- `AdelicSpaceSpreadProperMapStatement` (Proposition 5.8) and
  `AdelicSpaceSpreadSmoothOpenStatement` (Theorem 5.9) are the conjunctions of the two
  characteristics, in a common universe.

## Relation to the source and derived content

Conrad's topology on `Y(A_F)` for an algebraic space `Y` over `F` is defined through a
separated model of finite type over a ring of `S`-integers (printed p.17, paragraph
before Proposition 5.8). The statements are indexed by arbitrary separated models of
finite type of source and target, as in the published scheme statements
`AdelicSpreadProperMapStatement` (Proposition 4.4) and `AdelicSpreadSmoothOpenStatement`
(Theorem 4.5); they claim the conclusion for every choice. That the topology does not
depend on the model, and that every separated algebraic space of finite type over `F`
has such a model, are stated separately (the spread clauses of
`AdelicSpacePointTopologyStatement`). With them, the statements are Conrad's claims for
the topology he constructs.

"Separated algebraic spaces over `F`" is carried by the separated models: the generic
fibre of a separated model is separated. The conventions for the global fields (finite
constant field and nonempty `S` for function fields, finite places for number fields,
infinite places always included in the adeles) are those of the published
`AdelicSpaceLevelPointsStatement` and of the definitions in
`AdelicSpacePointTopology.lean`.

Proposition 5.8 assumes the spaces only locally of finite type. Conrad's adelic topology
on `X(A_F)` exists for separated spaces of finite type over `F` (printed p.17), so the
statement needs finite-type models of both spaces; this is stated as the qualification of
this unit. For a proper `g` with `W` of finite type, `Y` is of finite type as well, so
the restriction concerns only the target.

Conrad's "topologically proper" is formalized as Mathlib's `IsProperMap`, the Bourbaki
notion, as in the published `AdelicSpreadProperMapStatement`. The adelic points are
Hausdorff and locally compact (claimed on printed p.17, stated in
`AdelicSpacePointTopologyStatement`), and then Mathlib's
`isProperMap_iff_isCompact_preimage` shows that it agrees with the reading "continuous
with compact preimages of compact sets". "The fibers of `f` are geometrically
connected" is `HasGeometricallyConnectedFibres`: every fibre over a field-valued point is
connected and nonempty. Surjectivity already makes every fibre over a point nonempty.

Also derived here: the names and the packaging of the two characteristics.

## Not stated here

Conrad's proof of Proposition 5.8 carries over the proof of Proposition 4.4 using
Corollary 5.6 (stated as `LocalFieldProperPointMapStatement`). His proof of Theorem 5.9
carries over the scheme case and needs Lemma 4.6 for algebraic spaces of finite
presentation over `ℤ`, which rests on étale cohomology of noetherian algebraic spaces,
the Grothendieck–Lefschetz trace formula and Deligne's Riemann Hypothesis for separated
algebraic spaces of finite type over a finite field. These are proof material.
