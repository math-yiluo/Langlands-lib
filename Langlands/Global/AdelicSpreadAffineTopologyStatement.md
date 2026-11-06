# Agreement of the adelic spread topology with the affine topology

Author: Worker 105.

`AdelicSpreadAffineTopologyStatement` states a claim that Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), makes at the start of
Section 4, printed p.9, for global fields of both characteristics. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module only states
the claim and contains no proof.

Conrad writes on printed p.9: "Let `X` be a finite type `F`-scheme. We use Theorems 3.4
and 3.6 along with the bijection (3.5.1) to give `X(A_F)` a topological structure that is
functorial in `X` and coincides with the topology in Proposition 2.1 when `X` is affine."

## Objects

All objects are published Library definitions.

- `CurvePlaceAdelePoints k F Y` and `NumberFieldAdelePoints K Y` (from
  `Langlands/Global/AdelicGenericFiberPoints.lean`) are the actual points
  `RingPoint F Y A_F` of a scheme `Y` over the global field: morphisms
  `Spec A_F ⟶ Y` over the base field. The coefficient ring is
  `CurvePlaceAdeleRing k F` in the function-field case and Mathlib's full ring
  `Adeles K` in the number-field case, including every infinite factor.
- `curvePlaceSpreadAdelePointTopology k F S X Y e` and
  `numberFieldSpreadAdelePointTopology K S X Y e` (same module) are Conrad's adelic
  topology attached to a spread. Here `X` is a scheme over the ring of `S`-integers and
  `e` is an isomorphism from the actual generic fibre of `X` to `Y`. The topology is
  transported along the bijection (3.5.1) from the final topology on the points of `X`
  over the adelic levels `A_{F,T}`, `T ⊇ S`. Each level carries the topology of the
  product decomposition (3.6.1).
- For an affine scheme `Y` over the field, `RingPoint F Y A_F` carries the Library's
  affine point topology (from `Langlands/AlgebraicGeometry/PointTopology/AffineScheme.lean`).
  It is induced from the evaluation topology on algebra maps from the global sections of
  `Y` to `A_F`, which is the topology of Conrad's Proposition 2.1. In the statement it
  appears as `inferInstance`, under the hypothesis `[IsAffine Y.left]`.

## The statements

- `CurvePlaceSpreadAffineTopologyStatement`: let `k` be a perfect field and `F` a
  function field over `k` (Mathlib's `FunctionField k F`, with the compatible
  `RatFunc k`-algebra structure). Let `S` be a finite set of places
  `AlgebraicCurve.Place k F` and `X` a scheme over `Spec (curvePlaceSIntegers k F S)`
  whose structure morphism is locally of finite type and quasi-compact. Let `Y` be a
  scheme over `Spec F` whose underlying scheme is affine, and `e` an isomorphism from the
  generic fibre of `X` to `Y`. Then `curvePlaceSpreadAdelePointTopology k F S X Y e` is
  equal to the affine point topology on `CurvePlaceAdelePoints k F Y`.
- `NumberFieldSpreadAffineTopologyStatement`: the same with a number field `K`, a finite
  set `S` of finite places, a model `X` over Mathlib's `S`-integers
  `(S : Set (FinitePlace K)).integer K` and `numberFieldSpreadAdelePointTopology`.
- `AdelicSpreadAffineTopologyStatement` is the conjunction of the two, in a common
  universe.

## Relation to the source and derived content

Conrad's topology on `X(A_F)` is defined through a model over some ring of `S`-integers;
the published `AdelicSpreadTopologyIndependenceStatement` says that it does not depend on
the model. The statement quantifies over every finite-type model and every
generic-fibre isomorphism, so it says that the topology from any model is the affine
topology. The model `X` itself need not be affine, and its generic fibre is identified
with `Y` only through `e`. Finite type of `Y` over the field is not a separate
hypothesis: it follows from the existence of the finite-type model.

The scope conventions are those of the published spread statements, such as
`AdelicSpreadTopologyIndependenceStatement`. `S` may be empty. In the function-field
case the constant field is only assumed perfect. Conrad's global function fields have a
finite constant field, so this case is covered. The agreement argument does not use
finiteness of the constant field: see the proof route below.

Proof route, recorded for orientation only. After enlarging `S`, a finite-type model of an
affine scheme becomes affine (descent of affineness along the colimit of the `S`-integer
rings), and by model independence one may use such a model. For an affine model, the
product topology (3.6.1) on each level is the affine topology over `A_{F,T}`. `A_{F,T}`
is an open subring of `A_F` with the subspace topology, so each level maps by an open
embedding into `X(A_F)` with the affine topology. Every adelic point comes from some
level, by finite presentation. A final topology from a cover by continuous open maps
is the given topology.

Also derived here: the names and the packaging of the two characteristics.

## Not stated here

Functoriality of the adelic topology, its compatibility with fibre products and closed
immersions, its properties for separated schemes, and independence of the model are
separate published statements (`AdelicSpreadFunctorialityStatement`,
`AdelicSpreadProductStatement`, `AdelicSpreadClosedImmersionStatement`,
`AdelicSpreadTopologicalPropertiesStatement`, `AdelicSpreadTopologyIndependenceStatement`).
The comparison of the affine point topology with the evaluation topology on the
coefficient-point groups `G.affinePoints` of an affine group scheme is the published
`affinePointsRingPointHomeomorph` (from
`Langlands/GroupScheme/AffinePointRingPointComparison.lean`). No restricted-product
description of adelic points is stated here.
