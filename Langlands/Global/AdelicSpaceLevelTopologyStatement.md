# Topological properties of adelic-level points of algebraic spaces

Author: Worker 105.

`AdelicSpaceLevelTopologyStatement` states the topological claims that Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011), makes on
printed p.17 after Corollary 5.7, for global fields of both characteristics. The
registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module only
states the claims and contains no proof.

Conrad writes on printed p.17: "As an application of Corollary 5.7, we can carry over
verbatim the proof of Theorem 3.6 to show that for a separated algebraic space `X_S` of
finite type over `O_{F,S}`, the product topology on `X_S(A_{F,S})` via Proposition 5.2
and Proposition 5.4 is locally compact Hausdorff and induces an open embedding
`X_{S'}(A_{F,S'}) → X_{S''}(A_{F,S''})` where `X_{S'}` and `X_{S''}` are as in
Theorem 3.6." In Theorem 3.6 (printed p.6), `S' ⊆ S''` are finite sets of places
containing `S`, and `X_{S'}`, `X_{S''}` are the base changes of `X_S` over `O_{F,S'}`
and `O_{F,S''}`. As always in the paper, `S` is a finite nonempty set of places
containing the archimedean places (printed p.5).

## The statements

The topologies, base changes and change-of-level maps are the published definitions of
`Langlands/Global/AdelicSpaceLevelTopology.lean`. `FiniteTypeOverRing` is from
`Langlands/Global/AdelicSpaceLevelPointsStatement.lean`; it says that `X → Spec O` is
of finite type. `IsSeparated X` says that the diagonal of `X` is a representable
closed immersion.

- `NumberFieldSpaceLevelTopologyStatement`: let `K` be a number field, `S` a finite set
  of finite places, and `O = (S : Set (FinitePlace K)).integer K` Mathlib's ring of
  `S`-integers. Let `X` be an algebraic space over `Spec O` with `IsSeparated X` and
  `FiniteTypeOverRing O X`. Give `RingPoints O X (numberFieldAdeleLevel K S)` the
  topology `numberFieldSpaceLevelTopology K S X`. Then:
  1. this space is locally compact (`LocallyCompactSpace`) and Hausdorff (`T2Space`);
  2. for every finite set `T` of finite places with `S ⊆ T`, the change-of-level map
     `numberFieldSpaceLevelTransition K hST X` is an open embedding
     (`IsOpenEmbedding`). Its target is the set of `numberFieldAdeleLevel K T`-points
     of the base change `numberFieldSpaceLevelBaseChange K hST X` of `X` to the
     `T`-integers, with the topology `numberFieldSpaceLevelTopology K T` of that base
     change.
- `CurvePlaceSpaceLevelTopologyStatement`: let `k` be a finite field and `F` a function
  field over `k` (Mathlib's `FunctionField k F`). Let `S` be a nonempty finite set of
  places `AlgebraicCurve.Place k F`, and `O = curvePlaceSIntegers k F S`. For every
  algebraic space `X` over `Spec O` with `IsSeparated X` and `FiniteTypeOverRing O X`,
  the same two claims hold with `curvePlaceAdeleLevel`, `curvePlaceSpaceLevelTopology`,
  `curvePlaceSpaceLevelBaseChange` and `curvePlaceSpaceLevelTransition`. Here `T` is
  any finite set of places with `S ⊆ T`.
- `AdelicSpaceLevelTopologyStatement` is the conjunction of the two, in a common
  universe.

## Relation to the source and derived content

The topology `...SpaceLevelTopology` is induced along the map (3.6.1) from the product
of Conrad's topologies on the local factors. The definition module explains this and
its two derived choices: the topology is induced rather than transported through the
bijection of Proposition 5.2, and `X(O_v)` carries the topology induced from `X(F_v)`.
When (3.6.1) is bijective, which is Proposition 5.2
(`AdelicSpaceLevelPointsStatement`, not proved here), the induced topology is Conrad's
transported "product topology via Proposition 5.2 and Proposition 5.4". The statements
keep Conrad's hypotheses, separated and of finite type, so they make Conrad's claims
about his topology.

Conrad's open embedding goes from `X_{S'}(A_{F,S'})` to `X_{S''}(A_{F,S''})`, where
both spaces are base changes of a given `X_S`. The statement quantifies over every
separated finite type `X` over the `S`-integers and every `T ⊇ S`. Applied with `S'`
in the role of `S`, `X_{S'}` in the role of `X` and `S''` in the role of `T`, the map
goes from `X_{S'}(A_{F,S'})` to the points of the base change of `X_{S'}` over
`O_{F,S''}`. That space is Conrad's `X_{S''}` up to the canonical isomorphism between
an iterated base change and the direct base change. The statement does not formalize
this isomorphism. `X_{S'}` is again separated and of finite type over `O_{F,S'}`, so
the quantified form covers Conrad's claim modulo that isomorphism. The case `S' = S`
is literally covered.

For a number field, `S` ranges over finite sets of finite places. The archimedean
places are always factors of the level rings, as in Conrad's convention that `S`
contains them, and this makes Conrad's set nonempty. For a function field, Conrad's
nonemptiness is the hypothesis `S.Nonempty`; a superset `T` is then nonempty too.
"Global function field" is formalized as a function field over a finite constant field
`k`, with places `AlgebraicCurve.Place k F`. These conventions are those of
`AdelicSpaceLevelPointsStatement`.

Conrad's argument is the proof of Theorem 3.6 with Corollary 5.7 as input. Through the
bijection (3.6.1), local compactness follows from local compactness of the `X(F_v)`
(Proposition 5.4) and compactness of the `X(O_v)` for `v ∉ S`. The open embedding
follows because `X(O_v)` is open in `X(F_v)` and `X(O_v) → X(F_v)` is injective for
separated `X`. This route is recorded for orientation only; no proof is given here.

Also derived here: the names, the packaging of the two characteristics, and the
grouping of the three claims of the sentence into one proposition per characteristic.

## Not stated here

The bijectivity of `lim_{S'} X_S(A_{F,S'}) → X_S(A_F)` (Theorem 3.4 for algebraic
spaces), the resulting topology on `X(A_F)` for a separated algebraic space of finite
type over `F`, and its properties listed on printed p.17 (locally compact, Hausdorff,
countable base, compatibility with fibre products and closed immersions, and agreement
with the scheme case) are separate statements.
