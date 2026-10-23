# Points of restricted relative homomorphisms and the three-variable relative Hom functor

Author: Worker 281.

This module extends the published modules
`Langlands.GroupScheme.Cartier.Restriction` (restriction of relative
homomorphisms along test-scheme maps, the functor `relativeHomFunctor G H`, and
source precomposition) and `Langlands.GroupScheme.Cartier.RelativeHomPostcompose`
(target postcomposition). It imports both by Lean name and redefines neither.
Throughout, `G` and `H` are arbitrary commutative group schemes over a scheme `S`
(`Langlands.CommGroupScheme S`). `T` and `T'` are objects of `Over S`, and
`a : T' ⟶ T` is a morphism over `S`. `RelativeHom G H T` is the published actual
Hom group from `G_T = testBaseChange T G` to `H_T`, written additively. The
module has no finiteness or geometric hypotheses. It adds no pointwise group
homomorphism as an independent input.

## Restriction commutes with the canonical projections

`restrict_baseChangeProj` states that for `χ : RelativeHom G H T`, the
underlying scheme morphism of `restrict G H a χ`, followed by the canonical
projection `baseChangeProj H a : H ×_S T' ⟶ H ×_S T`, equals
`baseChangeProj G a` followed by the underlying morphism of `χ`. The proof
checks both pullback projections. On the first projection to `H` this is the
published defining formula `restrict_fst`. On the second projection the
equation holds because `restrict G H a χ` and `χ` are morphisms over `T'` and
`T`, respectively.

## The canonical identification of points

Let `U` be an object of `Over T'.left`, that is, a scheme over `T'`. Then
`(Over.map a.left).obj U` is `U` regarded as a scheme over `T` through `a`.
`restrictOverIso a U` is the isomorphism in `Over S` between `U` regarded over
`S` through `T` and `U` regarded over `S` through `T'`. Its underlying morphism
is the identity of `U`. The two structure morphisms agree because
`a.left ≫ T.hom = T'.hom`.

`restrictPointsEquiv G a U` is the group isomorphism from the `U`-points of
`G_{T'}` (morphisms `U ⟶ G_{T'}` over `T'.left`) to the `U`-points of `G_T`,
with `U` regarded over `T`. It is the composite of three isomorphisms:
- the published `baseChangePointsEquiv T'.hom G.toGrp U`, which identifies
  `U`-points of `G_{T'}` with `U`-points of `G` over `S`;
- precomposition with `restrictOverIso a U`, as an isomorphism of point groups
  of `G` given by the Yoneda functor `yonedaGrpObj G.X`;
- the inverse of `baseChangePointsEquiv T.hom G.toGrp` at `U` regarded over `T`.

Thus a point of `G_{T'}` and its image are the same point of `G`. This is stated
by `baseChangePointsEquiv_restrictPointsEquiv`: applying
`baseChangePointsEquiv T.hom` to the image gives
`(restrictOverIso a U).hom` composed with
`baseChangePointsEquiv T'.hom G.toGrp U x`.
`restrictPointsEquiv_left` gives the concrete form: the underlying scheme
morphism of the image of `x` is `x.left ≫ baseChangeProj G a`. The proof
compares both pullback projections. The first projection comes from
`baseChangePointsEquiv_restrictPointsEquiv`, since the underlying morphism of
`restrictOverIso a U` is the identity. The second comes from the structure
morphisms over `T'` and `T`.

## The point formula for restriction

`restrictPointsEquiv_restrict` is the point formula: for
`χ : RelativeHom G H T` and a `U`-point `x` of `G_{T'}`,

`restrictPointsEquiv H a U (x ≫ (restrict G H a χ).toMul.hom.hom) =
  restrictPointsEquiv G a U x ≫ χ.toMul.hom.hom`.

So the restricted homomorphism acts on `U`-points as `χ` acts on the same
points, with `U` regarded over `T`. The proof applies `restrictPointsEquiv_left`
on both sides and then uses `restrict_baseChangeProj`.

`baseChangePointsEquiv_restrict` restates the formula through the published
`baseChangePointsEquiv` identifications. The `U`-point of `H` over `S`
corresponding to `x ≫ (restrict G H a χ).toMul.hom.hom` equals
`(restrictOverIso a U).inv` composed with the `U`-point of `H` corresponding to
`restrictPointsEquiv G a U x ≫ χ.toMul.hom.hom` over `T`. In other words, the
restricted morphism pulls back `χ`, transported by the canonical
`baseChangePointsEquiv` identifications. Section evaluation is the special case
`U = T'` with its identity structure morphism. Its naturality in the test scheme
is the published `evaluation_restrict` from `Restriction`, which this module
does not repeat.

`restrict_baseChange_map` states that restricting the base change to `T` of a
homomorphism `f : G ⟶ H` along `a` gives its base change to `T'`. Both sides
are compared by `relativeHom_ext` on first projections, using `restrict_fst`,
`baseChange_map_fst` and `baseChangeProj_fst`.

## The three-variable relative Hom functor

`relativeHomTrifunctor` is the functor

`(CommGroupScheme S)ᵒᵖ ⥤ CommGroupScheme S ⥤ (Over S)ᵒᵖ ⥤ AddCommGrpCat`,

`(G, H, T) ↦ Hom_T(G_T, H_T)`. For fixed `G` its value is the published
target-covariant functor `relativeHomTargetFunctor G`, so `H` acts by
`postcomposeNatTrans`. A homomorphism `φ : G' ⟶ G` acts by the family of
published natural transformations `precomposeNatTrans H φ`. This family is
natural in `H` by the published commutation
`precomposeNatTrans_postcomposeNatTrans`. The identity and composition laws are
the published `precomposeNatTrans_id` and `precomposeNatTrans_comp`.
`relativeHomTrifunctor_obj_obj`, `relativeHomTrifunctor_obj_map` and
`relativeHomTrifunctor_map_app` record definitionally that the components are
`relativeHomFunctor G H`, `postcomposeNatTrans G ψ` and `precomposeNatTrans H φ`.
`relativeHomTrifunctor_flip_obj` states that fixing the target `H` gives the
published `relativeHomBifunctor H`.

## Provenance

These constructions are derived categorical infrastructure, not a new
theorem of the source. Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary draft, Definition (3.1), printed p.29/PDF33, defines group schemes
and their homomorphisms. The paragraph following it on that page notes that the
pullback `G ×_S S'` along `S' → S` is an `S'`-group scheme. Section (3.21), printed p.41/PDF45, defines the
contravariant group functor `Hom(G, Gm,S)` on `S`-schemes,
`T ↦ Hom_{T-GrSch}(G_T, Gm,T)`. This module works with an arbitrary commutative
group scheme `H` in place of `Gm,S`. It proves the canonical description of
restriction on `U`-points and packages the published restriction,
precomposition and postcomposition actions as one functor of three variables.
The point identification is the standard universal property of fibre products,
in the form of the published `baseChangePointsEquiv`. Cartier representability,
biduality and isogeny kernel duality are not claimed.

Registered source: `edixhoven-vandergeer-moonen-abelian-varieties-draft`.
SHA256: `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Retained file:
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
