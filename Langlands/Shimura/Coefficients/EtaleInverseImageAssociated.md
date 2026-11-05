# Inverse image of associated coefficient sheaves along arbitrary morphisms

This internal construction compares inverse image along an arbitrary
morphism of schemes with the existing invariant (associated) coefficient
sheaves of a cover with a group action. It constructs the base-change map
for product sheaves and the resulting comparison of associated sheaves. It
proves naturality, compatibility with deck transformations and with all
maps of cover objects, and the formula on invariant sections. For a finite
group it reduces invertibility of the associated comparison to invertibility
of the product-sheaf base-change map. All declarations are in namespace
`Langlands.Shimura.Coefficients`.

## Scope

This module constructs the maps and does not prove that they are
isomorphisms. The companion module
[EtaleInverseImageAssociatedIso](EtaleInverseImageAssociatedIso.md) proves
that the product-sheaf base-change map, and hence the associated-sheaf
comparison, is an isomorphism for finite geometric torsors. Together they give
the arbitrary-morphism analogue of the existing étale-restriction comparison
`etaleAssociatedPullback`. No constant-sheaf specialization, varying system,
cohomology or Shimura specialization is constructed here.

## Parameters and inputs

Let `X Z : Scheme.{u}`, let `f : Z ⟶ X` be any morphism, and let
`R : Type u` be a commutative ring. Sheaves are module sheaves on the small
étale sites. There is no étale, finiteness or other hypothesis on `f`.

The inputs are the existing constructed inverse image `inverseImage f R`, its
adjunction `inverseImageAdjunction f R` with the existing direct image
`directImage f`, and the existing geometric base change
`etaleObjectPullback f : X.Etale ⥤ Z.Etale`. The direct image evaluates a
sheaf on `Z` on base changes of objects over `X`. The existing
`productSheaf J V` is the sheaf `U ↦ F(V × U)`. The existing
`coverPullback J a F` restricts sections along `a × 𝟙` for a map `a` of
cover objects; `deckMap` is given by the same formula for an endomorphism. For a
group `G` and `Y : Action X.Etale G`, the existing `diagonalFunctor`,
`invariantDiagram`, `associatedFunctor` and `inclusion` form the associated
sheaf as the limit over `SingleObj G` of the diagonal action on
`productSheaf J Y.V`. The existing `etaleTorsorPullbackFunctor f G` is
geometric base change of actions.

## Direct image and product sheaves

`directImageProductSheafIso f R V` is the natural isomorphism

```text
directImage f ⋙ productSheaf X V ≅ productSheaf Z (P_f V) ⋙ directImage f,
```

where `P_f = etaleObjectPullback f`. At a sheaf `F` on `Z` and an object `U`,
the source is `F(P_f(V × U))` and the target is `F(P_f V × P_f U)`. The
component is `F` applied to the inverse of Mathlib's `prodComparison` for
`P_f`. That map is invertible because the existing instance makes `P_f`
preserve finite limits. Naturality in `U` is Mathlib's
`prodComparison_inv_natural`; naturality in `F` is naturality of sheaf maps.
`directImageProductSheafIso_deck` and
`directImageProductSheafIso_coverPullback` show that this isomorphism
intertwines `deckMap` and `coverPullback` along a map `a` of cover objects
with the same maps along `P_f a`. Both proofs use the same naturality of
`prodComparison`.

## The product-sheaf base-change map

For `V : X.Etale` and a sheaf `F` on `X`, `inverseImageProductSheafMap f R V F`
is a map

```text
inverseImage f (productSheaf X V F) ⟶ productSheaf Z (P_f V) (inverseImage f F).
```

It is the adjoint, under `inverseImageAdjunction`, of the product sheaf of
the adjunction unit at `F` followed by `directImageProductSheafIso` at the
inverse image of `F`. `homEquiv_inverseImageProductSheafMap` records this
defining adjoint.

- `inverseImageProductSheafMap_natural` proves naturality in `F`, and
  `inverseImageProductSheafNatTrans f R V` packages the map as a natural
  transformation `productSheaf X V ⋙ inverseImage f R ⟶ inverseImage f R ⋙
  productSheaf Z (P_f V)`.
- `inverseImageProductSheafMap_deck` proves that inverse image of
  `deckMap a F` followed by the map equals the map followed by
  `deckMap (P_f a)`, for every endomorphism `a` of `V`.
- `inverseImageProductSheafMap_coverPullback` proves the same equation for
  `coverPullback` along any map `a : V' ⟶ V` of cover objects.

Each proof applies the adjunction bijection. It then uses Mathlib's
`homEquiv` naturality, naturality of the unit, and the corresponding lemma
for `directImageProductSheafIso`.

## The associated-sheaf comparison

Let `G : Type u` be a group and `Y : Action X.Etale G`, and write `Y_f` for
`(etaleTorsorPullbackFunctor f G).obj Y`.

- `inverseImageDiagonalMap f R Y F` is the morphism of actions from inverse
  image of the diagonal action on `productSheaf X Y.V F.V` to the diagonal
  action for `Y_f` on the inverse-image coefficients. Its underlying map is
  `inverseImageProductSheafMap f R Y.V F.V`. Equivariance follows from the
  deck and naturality lemmas, since the action of `Y_f` is the base change of
  the action of `Y`. `inverseImageDiagonalNatTrans` records naturality in the
  coefficient action `F`.
- `inverseImageInvariantMap f R Y F` is the same map viewed as a natural
  transformation of invariant diagrams over `SingleObj G`.
- `inverseImageAssociatedMap f R Y` is the natural transformation

  ```text
  associatedFunctor X Y ⋙ inverseImage f R
    ⟶ (inverseImage f R).mapAction G ⋙ associatedFunctor Z Y_f.
  ```

  At `F` it is Mathlib's `limit.post` comparison from the inverse image of
  the invariant limit to the limit of inverse images, followed by `limMap` of
  `inverseImageInvariantMap`. Naturality is checked on the limit projection.
- `inverseImageAssociatedMap_inclusion` states that the comparison followed
  by the invariant inclusion for `Y_f` equals inverse image of the original
  invariant inclusion followed by `inverseImageProductSheafMap`.

## Finite groups

Assume `[Finite G]`. The category `SingleObj G` has objects in `Type` and
morphisms in `Type u`, so Mathlib's finite-limit preservation does not apply
to it directly. The instance `inverseImage_preservesLimitsOfShape_singleObj`
transports it along the equivalence
`(Shrink.mulEquiv.{0} (α := G)).toSingleObjEquiv` from the finite group
`Shrink.{0} G` in `Type`, using the existing finite-limit preservation of
`inverseImage f R`.

`isIso_inverseImageAssociatedMap_app` states that if
`inverseImageProductSheafMap f R Y.V F.V` is an isomorphism, then the
associated-sheaf comparison at `F` is an isomorphism. The limit comparison is
invertible by the preservation instance, and `limMap` of a componentwise
isomorphism is invertible.

## Provenance

This is internal categorical infrastructure built from Mathlib's
adjunction bijection, product comparison, limit comparison and the
equivalence of one-object categories induced by a group isomorphism. It uses
the existing constructed inverse image and direct image, geometric base
change, product sheaves and associated sheaves. No external-literature
statement is formalized.
