# Topological properties of adelic points of algebraic spaces

Author: Worker 105.

`AdelicSpacePointTopologyStatement` states the claims that Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), makes on printed p.17 about
adelic points of separated algebraic spaces of finite type, for global fields of both
characteristics. The registered source is `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module only
states the claims and contains no proofs.

Conrad writes on printed p.17: "Since Theorem 3.4 is valid for algebraic spaces, the natural
map `lim_{S'} X_S(A_{F,S'}) → X_S(A_F)` is bijective for any separated algebraic space `X_S`
of finite type over `O_{F,S}` (where `S'` varies through the finite sets of places containing
`S`). Thus, exactly as in the scheme case, we can functorially topologize `X(A_F)` for any
separated algebraic space `X` of finite type over `F` (recovering our earlier topological
constructions when `X` is a separated `F`-scheme of finite type). Exactly as in the scheme
case, this is locally compact, Hausdorff, has a countable base of opens, and is compatible
with fiber products and closed immersions." The scheme case is the start of Section 4
(printed p.9). There Conrad also says that the points of a separated model over
`O_{F,S}` form an open subset of `X(A_F)`.

## Objects

The topologies and maps are the definitions of `Langlands/Global/AdelicSpacePointTopology.lean`.
For an algebraic space `X` over the `S`-integers, `...SpaceStageTopology` is the topology on the
points over the level `A_{F,T}`, `T ⊇ S`. `...SpaceStageMap` maps them to the full adelic points
`...SpaceAdelePoints`. `...SpaceAdelePointTopology` is the final topology for these maps.
`...SpaceSpreadTopology S X Y e` is the topology on the adelic points of a space `Y` over the
field attached to a model `X` and an isomorphism `e` from the generic fibre
`...SpaceGenericFiber S X` to `Y`.

`IsSeparated X` (from `Langlands/AlgebraicGeometry/AlgebraicSpace/RingPoints.lean`) says that
the diagonal of `X` is a representable closed immersion. `FiniteTypeOverRing C X` (from
`Langlands/Global/AdelicSpaceLevelPointsStatement.lean`) says that `X` has an étale surjective
atlas by a scheme locally of finite type and quasi-compact over `Spec C`; with separatedness
this is Conrad's "separated of finite type". `IsClosedImmersion (hom f)` (from
`Langlands/AlgebraicGeometry/AlgebraicSpace/Thickening.lean`) says that `f` is representable
and every represented projection is a closed immersion of schemes. `schemeToSpace` regards a
scheme as an algebraic space, and `schemeRingPointsEquiv` identifies its points with the
scheme points.

## The statements

The function-field statements (`CurvePlace...`) concern a function field `F` over a finite
field `k` (Mathlib's `FunctionField k F`, with the compatible `RatFunc k`-algebra structure),
with places `AlgebraicCurve.Place k F` and a nonempty finite set `S`. The number-field
statements (`NumberField...`) concern a number field `K`, a finite set `S` of finite places
and Mathlib's `S`-integers; the infinite places are always factors of the levels and of
`Adeles K`.

- `...SpaceAdelePointsStatement`: let `X` be a separated algebraic space of finite type over
  the `S`-integers. Then:
  1. every adelic point of `X` is the image of a point over some level `A_{F,T}` under the
     stage map;
  2. every stage map is an open embedding (`IsOpenEmbedding`) for the stage topology and
     the adelic point topology;
  3. the adelic points are locally compact, Hausdorff and second countable.
- `...SpaceAdelePointMapsStatement`, for separated spaces of finite type over the
  `S`-integers:
  1. every morphism `f : X ⟶ Y` induces a continuous map `RingPoints.map f` on adelic points;
     if `f` is a closed immersion, the map is a closed embedding;
  2. for a pullback square `IsPullback p₁ p₂ f g` of such spaces, with `p₁ : P ⟶ X`,
     `p₂ : P ⟶ Y`, `f : X ⟶ Z`, `g : Y ⟶ Z`, the map `p ↦ (p₁(p), p₂(p))` from the adelic
     points of `P` to the product of those of `X` and `Y` is an embedding (`IsEmbedding`).
- `...SpaceAdelePointSchemeStatement`: for a scheme `U` over the `S`-integers whose structure
  morphism is locally of finite type, quasi-compact and separated, `schemeRingPointsEquiv` is
  a homeomorphism (`IsHomeomorph`). Its source is the adelic points of the associated
  algebraic space with the space topology. Its target is the scheme points with the published
  fixed-model topology `...FixedModelAdelePointTopology`.
- `...SpaceSpreadStatement`:
  1. every separated algebraic space `Y` of finite type over the field has a model: a finite
     set `S` (nonempty for function fields), a separated algebraic space `X` of finite type
     over the `S`-integers, and an isomorphism from the generic fibre of `X` to `Y`;
  2. for any two such models `(S, X, e)` and `(U, Z, f)` of the same `Y`, the attached
     topologies on the adelic points of `Y` are equal.
- `AdelicSpacePointTopologyStatement` is the conjunction of all eight, in a common universe.

## Relation to the source and derived content

Conrad's bijectivity of `lim_{S'} X_S(A_{F,S'}) → X_S(A_F)` is stated in two parts: every
adelic point comes from a level (part 1), and every stage map is injective, since it is an
open embedding (part 2). The transitions between levels are compatible with the stage maps,
so these two parts give bijectivity. Conrad's p.9 claim that the points of a separated model
form an open subset is part 2. The definitions use the final topology on `X_S(A_F)`, which
agrees with Conrad's transported colimit topology once bijectivity holds.

"Compatible with fiber products" is formalized as the embedding property of part 2 of the maps
statement. The image of `p ↦ (p₁(p), p₂(p))` is the set-theoretic fibre product, so the claim
says that the fibre product of adelic points carries the subspace topology of the product.
The pullback square is assumed to consist of separated spaces of finite type; this holds for
the fibre product of such spaces, but that fact is not stated here. "Functorially
topologize" is formalized as the continuity of `RingPoints.map f`. Morphisms are over the
`S`-integers, and the claim for spaces over the field follows through models.

"Recovering our earlier topological constructions" is the scheme statement. It compares with
the published fixed-model topology of the scheme over the `S`-integers. Topologies on spaces
over the field are compared through models, and the model-independence clause covers the
rest.

Conrad's topology on `X(A_F)` for a space over the field requires a model. Existence of a
model (Theorem 3.4 for algebraic spaces) and independence of the model are stated in the
spread statement. Separatedness is assumed for the models, as for Conrad's spaces.

Conrad's conventions for global fields are used: function fields have a finite constant
field, and `S` is nonempty for function fields. For number fields, `S` ranges over finite
sets of finite places, since the archimedean places are always included. These are the
conventions of the published `AdelicSpaceLevelPointsStatement`.

Also derived here: the names, the grouping of Conrad's claims into four propositions per
characteristic, and the formulations of bijectivity and of fibre-product compatibility
explained above.

## Not stated here

Proposition 5.8 (properness of adelic maps for proper maps), Theorem 5.9 (openness for
smooth surjective maps), and Proposition 5.14 (Weil restriction) are separate statements.
