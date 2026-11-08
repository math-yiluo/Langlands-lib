# Identity normalization of geometric inverse-image product coordinates

This internal construction proves the identity law for the actual product-sheaf
comparison of geometric inverse image. It retains the literal pullback cover and
its canonical comparison with the original cover. Its constant-coefficient
specialization supplies an identity law for `inverseImageConstantProductMap`.

## Objects and notation

Fix a universe `u`, a scheme `X : Scheme.{u}`, a commutative ring `R : Type u`,
an arbitrary object `V : X.Etale` and a sheaf
`F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)`. Write:

- `I` for `inverseImage (𝟙 X) R`, the already constructed geometric inverse image;
- `ι_H : I(H) ⟶ H` for `(inverseImageId R X).hom.app H`;
- `pV` for `(etaleObjectPullback (𝟙 X)).obj V`;
- `c_V : pV ≅ V` for `(etaleObjectPullbackId X).app V`;
- `P_V` for `productSheaf X.smallEtaleTopology V`;
- `a*` for `coverPullback X.smallEtaleTopology a`, contravariant in the cover.

Thus `P_V(F)` evaluates on an etale test object `W` by `F(V × W)`. The morphism
`a : V' ⟶ V` induces `a*_F : P_V(F) ⟶ P_V'(F)`. The object `pV` is the actual
fiber product along the identity, and is not identified definitionally with `V`.
In particular, `c_V.hom : pV ⟶ V` and `c_V.inv : V ⟶ pV` are both retained.

The geometric inverse image here is the existing small-etale construction using
affine-site restriction, left Kan extension and sheafification, with its
constructed adjunction. Its identity isomorphism `inverseImageId` is the
canonical comparison for that construction. No arbitrary inverse-image functor
or identity comparison is an input.

## Identity equation before cover normalization

Write `B(V,F)` for `inverseImageProductSheafMap (𝟙 X) R V F`, with type

```text
B(V,F) : I(P_V(F)) ⟶ P_pV(I(F)).
```

`inverseImageProductSheafMap_id` proves the equation

```text
B(V,F) ; P_pV(ι_F) = ι_(P_V(F)) ; (c_V.hom)*_F.
```

Both sides end in `P_pV(F)`. The proof uses the published comparison
`inverseImageIsoRestriction` with etale restriction. The identity is etale, so
that comparison applies without a new hypothesis. If `η_H` is its forward
component and `r_H` is the restriction identity component, the published
`inverseImageIsoRestriction_id` gives `η_H ; r_H = ι_H`. Cancelling the
isomorphism component gives `η_F.inv ; ι_F = r_F`.

The existing `inverseImageProductSheafMap_etale` expresses `B(V,F)` through the
restriction product comparison and the inverse of `η_F`. Substitution of the
last equation and `etaleProductSheafPullback_id` reduces the result to
`η_(P_V(F)) ; r_(P_V(F)) = ι_(P_V(F))`. This proves the displayed equation
with the actual cover comparison still present. The theorem has a reassociated
form for use inside longer composites.

## Constructed normalized identity map

The selected definition `inverseImageProductIdentityMap R V F` is the composite

```text
I(P_V(F)) --B(V,F)--> P_pV(I(F))
          --P_pV(ι_F)--> P_pV(F)
          --(c_V.inv)*_F--> P_V(F).
```

`inverseImageProductIdentityMap_eq` proves that this constructed composite equals
`ι_(P_V(F))`. After the preceding identity equation, the two cover restrictions
combine by `coverPullback_comp`. The equation
`c_V.inv ; c_V.hom = 𝟙 V`, followed by `coverPullback_id` and the categorical
identity law, finishes the proof. Thus the result identifies an explicitly
constructed map with the canonical inverse-image identity; that equality is not
supplied as data.

For every morphism `a : F ⟶ F'`,
`inverseImageProductIdentityMap_natural` proves

```text
I(P_V(a)) ; inverseImageProductIdentityMap R V F'
  = inverseImageProductIdentityMap R V F ; P_V(a).
```

The proof rewrites both normalized maps by their proved equality to `ι` and
uses naturality of `inverseImageId.hom`. This theorem also has a reassociated
form. It is natural in every coefficient sheaf, without an action or finiteness
premise.

## Constant coefficients

For any `M : ModuleCat.{u} R`, let `C(M)` be the constant sheaf on `X`.
`inverseImageConstantProductMap_id` proves

```text
inverseImageConstantProductMap (𝟙 X) R V M ; (c_V.inv)*_(C(M))
  = ι_(P_V(C(M))).
```

The existing constant-product map is `B(V,C(M))` followed by `P_pV` applied to
`inverseImageConstantIso.hom.app M`. The published
`inverseImageConstantIso_id` identifies that coefficient comparison with
`ι_(C(M))`. Unfolding, applying this coefficient identity and reassociating give
exactly `inverseImageProductIdentityMap_eq`. The actual inverse cover comparison
is retained, and the theorem has a reassociated form.

## Provenance and scope

This is an internal deduction from `EtaleInverseImageAssociatedIso`,
`EtaleInverseImageRestrictionCoherence`, `EtaleProductPullbackCoherence`,
`EtaleInverseImageConstant` and the separately constructed
`EtaleInverseImageConstantProduct`. It asserts no new theorem from external
literature. The identity and naturality equations are proved from those actual
constructions, and no desired CM conclusion is assumed.

The construction works for every scheme, etale cover object, commutative
coefficient ring and sheaf in the stated universe. There is no group, torsor,
rigidity or finiteness premise. This unit does not construct a CM identity
comparison or prove its compatibility with original lattice inclusions. Those
consumer results, general commensurability, rational adic independence, Hecke
compatibility, representability, canonical models and the exact Harris geometry
remain separate obligations.
