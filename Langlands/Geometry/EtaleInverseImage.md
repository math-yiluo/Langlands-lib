# Constructed inverse image on small etale sites

This module constructs inverse image of module sheaves along an arbitrary
scheme morphism `f : Z ⟶ X`, together with its adjunction to the actual
direct-image functor from `Langlands.Geometry.EtaleDirectImage`. It restricts
the source to the affine etale site, constructs left Kan extension along
geometric base change, and sheafifies on the target. The affine/small-etale
sheaf equivalence then transports the adjunction to the original source site.

Both schemes, the commutative ring `R`, and the module carriers have universe
`u`. In particular the construction retains `ModuleCat.{u} R`. Neither
etaleness of `f` nor any Noetherian, finite-type, finiteness or field
hypothesis is imposed. No inverse-image functor, Kan-extension existence,
adjunction or comparison is an input.

This is internal categorical infrastructure, derived from the actual
geometric base-change functor and Mathlib's affine etale site, comma-category
smallness, Kan-extension, sheafification and adjunction constructions. It
makes no new external-literature attribution or Harris specialization claim.

## An essentially-small source for Kan extension

Write `P_f : X.Etale ⥤ Z.Etale` for the actual geometric pullback functor,
`S_X : X.AffineEtale ⥤ X.Etale` for `Scheme.AffineEtale.Spec X`, and
`G_f := S_X ⋙ P_f`. The declaration `affineSiteMap` is this composite.
It uses scheme fiber products. Its target objects need not be affine.
`affineSiteMap_isContinuous` composes the two existing continuity
instances, for the affine etale topology on the source and the small
etale topology on the target.

The category `X.AffineEtale` is essentially small in universe `u`, and
`Z.Etale` is locally small in that universe. Consequently, for every
`V : Z.Etaleᵒᵖ`, the category
`CostructuredArrow G_f.op V` is essentially small in universe `u`.
Its objects are affine etale `X`-objects `U` with an arrow
`V.unop ⟶ G_f.obj U`. Its arrows are the compatible morphisms in the
opposite affine etale category.

`affineSiteMap_hasPointwiseLeftKanExtension` supplies the actual comma
colimits of any presheaf
`F : X.AffineEtaleᵒᵖ ⥤ ModuleCat.{u} R`. It applies
`HasColimitsOfShape.of_essentiallySmall` to the module category and
each comma category. The existing small colimits of modules therefore
suffice; colimits over an arbitrary large index category are never
assumed. Mathlib's pointwise Kan-extension construction then supplies
`G_f.op.HasLeftKanExtension F`.

## Kan extension followed by sheafification

`affineInverseImage f R` is the explicit composite

```text
sheafToPresheaf
  ⋙ G_f.op.lan
  ⋙ presheafToSheaf Z.smallEtaleTopology (ModuleCat R).
```

The source sheaves use `Scheme.AffineEtale.topology X`. The intermediate
presheaves use the full target category `Z.Etale`; target
sheafification is Mathlib's actual module-sheaf construction on that
site. `affineAdjunction` uses the Kan-extension/precomposition
adjunction, followed by the sheafification adjunction, restricted
through the fully faithful source inclusion. Its right adjoint is
precomposition by `G_f.op` on sheaves.

## Transport to the original small etale source site

Let
`E := Scheme.AffineEtale.sheafEquiv X (ModuleCat.{u} R)`.
Its inverse functor is restriction from the small etale site of `X`
to its affine etale subsite. The constructed functor is

```text
inverseImage f R := E.inverse ⋙ affineInverseImage f R.
```

Compose `E.symm.toAdjunction` with `affineAdjunction`. The resulting
right adjoint is `G_f`-precomposition followed by `E.functor`.
Precomposition by `G_f.op` is definitionally direct image followed
by `E.inverse`. `directImageFromAffineIso` reassociates these
functors and uses `E.counitIso` to identify that right adjoint
with `EtaleDirectImage.directImage f (ModuleCat.{u} R)`.

`inverseImageAdjunction` transports the constructed adjunction
through this isomorphism. It therefore supplies the actual natural
Hom equivalences, unit, counit and triangle identities between
the displayed inverse image and geometric direct image.
`inverseImage_isLeftAdjoint` and `directImage_isRightAdjoint`
expose these proved properties as instances.

Finite-limit preservation and exactness of inverse image, comparison
with the previously constructed restriction along an etale morphism,
identity and composition coherence, coefficient-sheaf comparisons,
algebraic-closure base change, supports, derived images and Harris
specialization remain separate constructions or proof obligations.
