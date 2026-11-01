# Unit and composition coherence of product-sheaf base change

Author: Worker 13.

This is internal derived infrastructure for the actual small-etale product and
restriction constructions. It uses the published `EtaleProductPullback`,
`EtaleAssociatedPullback`, `EtaleTorsorPullbackFunctoriality`, and `CrossCover`
modules and Mathlib's over-category comparisons. It asserts no comparison theorem
from Harris or Berkovich and has no external literature dependency.

All schemes, the commutative coefficient ring `R`, and module carriers lie in
universe `u`. The base maps `f : Z ⟶ X` and `g : W ⟶ Z` are etale. This hypothesis
allows the functor `S_f = EtalePullback.siteMap f` to send an etale object over
`Z` to the same scheme with its structure map composed with `f`. Write
`P_f = etaleObjectPullback f` for the actual scheme fiber-product functor,
`r_f` for restriction of module sheaves, and `B_V` for `productSheaf` at `V`.
Thus `(B_V F)(U) = F(V × U)`, with the product taken in the small-etale category.

The existing geometric comparison is

`χ_f(V,U) : S_f(P_f(V) × U) ⟶ V × S_f(U)`.

Its underlying scheme map is determined by the first fiber projection on the
first product factor and the unchanged second factor. The existing natural
isomorphism `θ_f(V) = etaleProductSheafPullback f R V` has type
`B_V ⋙ r_f ≅ r_f ⋙ B_(P_f V)` and components `F.map (χ_f(V,U)).op`.

## Geometric composition

Let `C_V : P_(g ≫ f)(V) ⟶ P_g(P_f(V))` be the hom component of Mathlib's
`Over.pullbackComp g f`. Let
`m_U : S_(g ≫ f)(U) ⟶ S_f(S_g(U))` be the hom component of `Over.mapComp`.
The latter has the identity underlying scheme map but retains the structural
identification between the two over-category objects.

`etalePullbackProjection_comp` states that `S_(g ≫ f)(C_V)`, followed by the
appropriate `m` and the two successive first projections, equals the single
first projection for `g ≫ f`.

`etaleProductPullbackHom_comp` proves

`χ_(g ≫ f)(V,U) ≫ (id_V × m_U)`

`= S_(g ≫ f)(C_V × id_U) ≫ m_(P_g(P_f(V)) × U)`

`  ≫ S_f(χ_g(P_f(V),U)) ≫ χ_f(V,S_g(U))`.

The two sides have the same source and target in `X.Etale`. The proof compares
their two product coordinates and then passes to the underlying scheme maps.
It records the coordinate identities for the five individual maps explicitly.
The first coordinate is the successive fiber-projection formula from
`Over.pullbackComp_left_fst_fst`; the second coordinate is unchanged throughout.
No geometric compatibility is supplied as a hypothesis.

## Geometric identity

Let `s : S_id ≅ Id` be `Over.mapId`, and let
`p_V : P_id(V) ⟶ V` be the first-projection hom of `etaleObjectPullbackId X`.
`etaleProductPullbackHom_id` proves

`s.inv_(P_id(V) × U) ≫ χ_id(V,U)`

`= (p_V × id_U) ≫ (id_V × s.inv_U)`.

The proof uses product extensionality. After forgetting to scheme maps, the
site-identification maps are identities and the comparison's coordinates are
exactly the first fiber projection and the second product projection.

## Natural comparison and sheaf laws

`etaleProductSheafPullbackComp` constructs a natural isomorphism

`(B_V ⋙ r_f) ⋙ r_g ≅ r_(g ≫ f) ⋙ B_(P_(g ≫ f)(V))`.

It is the functor associator followed by the restriction-composition
isomorphism whiskered by `B_V`, then `θ_(g ≫ f)(V)`. Its hom-component formula
`etaleProductSheafPullbackComp_hom_app` removes the identity associator component.

Write `c_F : r_g(r_f(F)) ⟶ r_(g ≫ f)(F)` for the hom of `restrictionComp`.
`etaleProductSheafPullback_comp` proves the component equation

`c_(B_V(F)) ≫ θ_(g ≫ f)(V)_F`

`= r_g(θ_f(V)_F) ≫ θ_g(P_f(V))_(r_f(F))`

`  ≫ B_(P_g(P_f(V)))(c_F) ≫ coverPullback(C_V, r_(g ≫ f)(F))`.

Here `coverPullback(C_V, -)` goes from the product sheaf for the iterated cover
to that for the single cover: it is contravariant in the cover. This direction
is essential to the equation. The equality describes the constructed two-step
natural comparison on every sheaf and every small-etale test object.

For `i_F : r_id(F) ⟶ F`, the hom of `restrictionId`,
`etaleProductSheafPullback_id` proves

`θ_id(V)_F ≫ B_(P_id(V))(i_F)`

`= i_(B_V(F)) ≫ coverPullback(p_V,F)`.

Both sheaf proofs apply sheaf and natural-transformation extensionality,
combine the contravariant presheaf maps by functoriality, and apply the respective
proved geometric equation. They use the actual existing comparison components,
without choosing new or assumed sheaf comparisons.

These constructions and laws apply to every small-etale cover object and every
module sheaf, without finite-cover, torsor, or local-constancy hypotheses.
Coherence on associated invariant sheaves, on constant coefficients, and on
whole varying-group coefficient systems is left to subsequent constructions.
Arbitrary non-etale inverse image, algebraic-closure base change, compact
supports, and actual Shimura realizations are also outside this focused unit.
