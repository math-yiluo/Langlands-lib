# Unit and composition coherence of associated coefficient-sheaf base change

Author: Worker 13.

This is internal derived infrastructure for the actual associated invariant
sheaf. It extends `EtaleAssociatedPullback` using the product-sheaf equations
in `EtaleProductPullbackCoherence`, the actual geometric cover comparisons,
and the invariant universal property from `Associated` and `CrossCover`.
It makes no claim to prove a named theorem of Harris or Berkovich.

All schemes, the commutative coefficient ring `R`, its module carriers and the
deck group `G` use universe `u`. Let `f : Z ⟶ X` and `g : W ⟶ Z` be etale
scheme morphisms. Write `r_f` for the existing restriction functor on small-etale
module sheaves, `P_f` for the actual cover pullback, `A_Y` for the associated
invariant-sheaf functor for an action `Y : Action X.Etale G`, and `B_V` for
`productSheaf` at a cover object `V`. Thus `P_f(V)` is the actual fiber product,
and `A_Y(F)` is the categorical invariant subsheaf of `B_(Y.V)(F.V)` under the
inverse deck pullback together with the coefficient action.

`Y` and the sheaf-valued coefficient representation `F` are arbitrary. The
construction does not require finiteness of `G`, a torsor hypothesis, or local
constancy of `F`. Etaleness of `f` and `g` is required by the existing
postcomposition functors on their small-etale sites.

`etaleCoefficientRestrictionId R X G` identifies the entire coefficient action
after identity restriction with the original action. It is
`Functor.mapActionCongr` applied to `EtalePullback.restrictionId`. Its underlying
map at `F` is precisely `restrictionId.hom.app F.V`, as recorded by
`etaleCoefficientRestrictionId_hom_app_hom`.

`etaleCoefficientRestrictionComp f g R G` identifies two successive restrictions
of the entire coefficient action with restriction along `g ≫ f`. It first uses
the inverse of `Functor.mapActionComp` and then `Functor.mapActionCongr` applied
to `EtalePullback.restrictionComp`. Its underlying map is the original
restriction-composition map at `F.V`, by
`etaleCoefficientRestrictionComp_hom_app_hom`. The auxiliary identity component
of `mapActionComp` is removed by the category identity law.

`etaleAssociatedPullbackComp f g R Y` is the natural isomorphism

```text
(A_Y ⋙ r_f) ⋙ r_g ≅ (r_(g≫f)).mapAction G ⋙ A_(P_(g≫f)(Y)).
```

It is assembled from the functor associator, restriction composition whiskered
by `A_Y`, and the existing associated-sheaf comparison for `g ≫ f`. The lemma
`etaleAssociatedPullbackComp_hom_app` identifies its component with
restriction composition on `A_Y(F)` followed by the single associated-sheaf
comparison. Naturality and invertibility come from these actual natural
isomorphisms; no comparison or coherence equation is supplied as input.

For the identity law, let `p : P_id(Y) ⟶ Y` be the first-projection equivariant
cover comparison `etaleTorsorPullbackId.hom.app Y`, and let `η_F` be the coefficient
identity comparison just defined. The theorem `etaleAssociatedPullback_id`
states

```text
associatedComparison_id(F) ≫ A_(P_id(Y)).map(η_F)
  = restrictionId_(A_Y(F)) ≫ crossCoverMap(id_G, p, id_F).
```

Both sides map the identity restriction of `A_Y(F)` to the associated sheaf
for `P_id(Y)` with the original coefficients `F`. The cover map points from
the pulled-back cover to the original cover. Consequently it induces the
opposite direction on associated sheaves; it is not silently replaced by a
definitional identification of covers.

For the composition law, let `C : P_(g≫f)(Y) ⟶ P_g(P_f(Y))` be the actual
equivariant single-to-iterated cover comparison
`etaleTorsorPullbackComp.hom.app Y`, and let `κ_F` be the coefficient composition
comparison. The theorem `etaleAssociatedPullback_comp` states

```text
restrictionComp_(A_Y(F)) ≫ associatedComparison_(g≫f)(F)
  = r_g.map(associatedComparison_f(F))
      ≫ associatedComparison_g(r_f(F))
      ≫ A_(P_g(P_f(Y))).map(κ_F)
      ≫ crossCoverMap(id_G, C, id_(r_(g≫f)(F))).
```

The final cross-cover map carries the associated sheaf for the iterated cover
to that for the single cover, with the same once-restricted coefficients. This
is the contravariant direction forced by the actual cover map `C`. In
particular, the right side retains both coefficient identification and the
geometric fiber-product comparison.

Both proofs use `hom_ext` for the invariant sheaf. The formula for
`crossCoverMap_inclusion`, naturality of the invariant inclusion in coefficient
maps, and `etaleAssociatedPullback_hom_inclusion` reduce the equations to maps
between product sheaves. In the identity case the product-sheaf identity law
and naturality of `restrictionId` give the result. In the composition case
restriction functoriality combines the two invariant inclusions; naturality
of `restrictionComp` and the product-sheaf composition law then identify the
two routes. Thus the intrinsic coherence is derived from the actual maps.

This pair supplies identity and binary-composition coherence for arbitrary
sheaf-valued coefficients. Constant-coefficient and whole varying-group system
coherence, non-etale inverse image, algebraic-closure base change, compact
supports and actual Shimura realizations remain separate obligations. It does
not assert that the entire Harris framework is complete.
