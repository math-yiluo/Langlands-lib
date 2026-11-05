# Smoothness of the derived-cover and maximal-torus multiplication map

Author: Worker 133. Worker 1637 supplied the consumer motivation and proposed
geometric route in the task specification.

`Langlands.GroupScheme.DerivedCoverTorusProductSmoothStatement` is a
`Prop`-valued definition. This module states a smoothness assertion and
contains no proof of it.

## Exact statement

For every field `k : Type u`, with arbitrary universe `u`, take actual group
schemes `H`, `D`, `C` over `Spec k`, a commutative group scheme `T` over the
same base, and homomorphisms

```text
d : D → H,       π : C → D,       i : T → H.
```

The hypotheses are precisely `IsSimplyConnectedDerivedCover d π` and
`IsMaximalTorus i`. The conclusion is

```lean
Smooth (subgroupProductMap (π ≫ d) i).left
```

The first hypothesis is the existing predicate from
[`SimplyConnected.DerivedCover`](DerivedCover.md). It includes connected
reductivity of `H`, the actual full scheme-theoretic derived-subgroup
inclusion `d`, and the simply connected central cover `π` of `D`.
In particular, the covering condition is on `π : C → D`; the ambient
composite is `π ≫ d : C → H`.

The second hypothesis is the existing predicate from
[`Torus.Maximal`](../Torus/Maximal.md). It says that `T` is a torus, that
`i` is a closed subgroup inclusion, and that any factorization of `i`
through a closed torus forces the map from `T` to that torus to be an
isomorphism.

The map is the existing actual morphism from
[`Rational.ProductDetection`](../Rational/ProductDetection.md), formed in
schemes over `Spec k`:

```text
C ×ₖ T → H,       (c,t) ↦ d(π(c)) · i(t).
```

Its `.left` is the underlying morphism of schemes. `Smooth` is
`AlgebraicGeometry.Smooth`, the scheme-morphism property, rather than
openness or surjectivity of a map on rational points. The construction uses
the indicated order of multiplication and does not require the two images
to commute.

The statement applies over arbitrary fields, including imperfect fields
and positive characteristic. It assumes neither smoothness nor étaleness
of `π`, and it places no smoothness premise on the displayed product map.
Existence of the supplied groups, inclusions and cover is separate.

## Internal provenance and intended geometric route

This is derived internal infrastructure for the Bruhat–Tits application
below, rather than a verbatim assertion in that source. Its mathematical
rationale is the following prospective proof, which is not implemented in
this module.

Let `S = C ×_H T` be the scheme-theoretic inverse image of `T` in `C`,
with map `λ : S → T`. The structural inputs are that `T ∩ D` is a maximal
torus of `D`, its inverse image under the central isogeny `π` is a maximal
torus of `C`, and `D · T = H`. In particular, `S` is smooth even when the
finite central kernel of `π` is not smooth.

The right action

```text
(c,t) · s = (c s, λ(s)⁻¹ t)
```

preserves the product map. The expected torsor identification makes
`C ×ₖ T → H` an `S`-torsor and yields smoothness from smoothness of `S`.
These structural and torsor assertions remain proof obligations. They may
be established after extension to an algebraic closure and then descended;
algebraic closure is not a hypothesis of the statement.

## Original-source motivation and scope

Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach* (2023), source
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
Fact 2.6.22, Definition 2.6.23 and Lemma 2.6.24, printed pp.104–105
(PDF pp.135–136), motivate the target. They define `G(k)♮` as the image
of `G_sc(k)`. For quasi-split `G`, Definition 2.6.23 uses a maximally split
maximal torus and sets `G(k)⁰ = G(k)♮ · T(k)⁰`. Lemma 2.6.24 asserts
openness of the resulting subgroup. The book does not state the present
arbitrary-field scheme-smoothness assertion in those passages.

The authors' *Corrections and additions* (version of 1 November 2024),
source `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp.24–25, were read with that passage. The correction preceding
Definition 2.6.20 assumes a Henselian valued field with perfect residue
field for the rest of that section. Those assumptions concern the
valued-field application; they are not premises of this internal
algebraic smoothness target.

For that application, a separate theorem that smooth morphisms induce
open maps on rational points over the relevant Henselian valued field,
together with openness of `T(k)⁰`, would make the image of
`C(k) × T(k)⁰` an open neighborhood inside the zero subgroup. No such
rational-point theorem, subgroup openness, compactness or topology is
asserted here. In characteristic `p`, the central cover `SL_p → PGL_p`
has a nonsmooth kernel, so one cannot replace the product-map target by a
smoothness assumption on the cover alone.

An exact-target proof is required separately after publication of this
statement.
