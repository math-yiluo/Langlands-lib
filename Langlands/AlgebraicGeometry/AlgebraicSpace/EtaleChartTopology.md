# The étale-chart topology on rational points of algebraic spaces

Author: Worker 105.

This module defines the topology that Brian Conrad, *Weil and Grothendieck approaches
to adelic points* (December 31, 2011), constructs in the proof of Proposition 5.4. The
registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module only
makes the definition and records its universal property. It proves none of the
properties asserted in Proposition 5.4.

Conrad writes on printed p.15: "To prove existence with the asserted properties,
consider the étale maps `f : U → X` from finite type `k`-schemes `U`. As we vary
through such maps, the images `f(U(k)) ⊆ X(k)` cover `X(k)`. We claim that the
strongest topology on `X(k)` making the maps `U(k) → X(k)` continuous (i.e., a subset
of `X(k)` is open when its preimage in each such `U(k)` is open) does the job."

## Definitions

Let `K : Type u` be a field with a topology, and let
`X : AlgebraicSpace (Spec (CommRingCat.of K))` be an actual algebraic space over
`Spec K` (from `Langlands/AlgebraicGeometry/AlgebraicSpace/Basic.lean`).

- `EtaleFiniteTypeChart K X` is the type of Conrad's charts. A chart consists of an
  actual scheme `scheme : Over (Spec (CommRingCat.of K))` and a morphism
  `hom : (schemeToSpace _).obj scheme ⟶ X` of algebraic spaces whose underlying
  transformation is étale in the Library sense `IsEtale` (representable, with every
  represented base change étale). The structure morphism `scheme.hom` must be locally
  of finite type and quasi-compact, that is, of finite type over `Spec K`.
- `EtaleFiniteTypeChart.pointMap c` is the map `U(K) → X(K)`. It sends a relative
  scheme point `x : RingPoint K c.scheme K` (a morphism `Spec K ⟶ U` over `Spec K`)
  to `RingPoints.map c.hom ((schemeRingPointsEquiv K c.scheme K).symm x)`, its image
  in `RingPoints K X K`.
- `etaleChartTopology K X` is the supremum over all charts `c` of the topologies
  coinduced by `c.pointMap` from `schemePointTopology K c.scheme K`. Here
  `schemePointTopology` is the Library's topology on rational points of schemes, the
  final topology of the affine open charts. In Mathlib's order on topologies, this
  supremum is the strongest topology making every chart map continuous.

## Universal property

- `etaleChartTopology_isOpen_iff`: a set `V ⊆ X(K)` is open exactly when its preimage
  under every chart map is open. This is Conrad's parenthetical description.
- `EtaleFiniteTypeChart.continuous_pointMap`: every chart map is continuous.
- `etaleChartTopology_continuous_iff`: a map out of `X(K)` is continuous exactly when
  its composite with every chart map is continuous.

## Relation to the source

The charts are exactly Conrad's étale maps `U → X` from finite type `K`-schemes,
with the existing scheme point topology on `U(K)`. The definition makes sense for any
topological field and any algebraic space over it. Conrad uses it for henselian
valued fields and for quasi-separated spaces locally of finite type, and the
properties he claims for it are stated separately (Proposition 5.4,
`HenselianSpacePointTopologyStatement`). Conrad's remark that the images of the
chart maps cover `X(k)` is not used in the definition. Also derived here: the names
and the packaging of charts as a structure.
