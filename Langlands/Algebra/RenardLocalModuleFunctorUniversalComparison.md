# Universal-property comparison of the chosen local-module functor

Author: Worker 1603. All declarations are in
`Langlands.Renard.ModuleLocalization.UniversalComparison`. This internal construction packages
the published objects and maps from
[RenardLocalModuleCategory](RenardLocalModuleCategory.md) into a functor and
identifies that functor naturally with a specified Mathlib model.

## Provenance and scope

The motivation is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.III.1, printed
pp.251–252 / PDF257–258, especially example 4 on PDF258. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Those two original pages were read for this construction. Example 4 views
the localized module as a module over the original ring and uses the full
subcategory of modules on which denominators act invertibly. The imported
`IsSLocal` expresses invertibility in the actual endomorphism ring. The
source's stronger scalar-inverse parenthesis is rejected by the published
integer/rational counterexample in
[RenardModuleLocalization](RenardModuleLocalization.md); see also the
[Appendix A corrections](../../notes/renard/appendix-a-corrections.md).

The functors, explicit carrier transports, natural transformations and
comparison below are internal packaging of these already published
constructions. They are not a literal new assertion in Renard. They reuse
Mathlib at commit `5ed2965256430c3649e86755f9576b54eca72435`, principally
`Algebra/Category/ModuleCat/Localization.lean`, `Ulift.lean`,
`ChangeOfRings.lean`, and `Algebra/Module/LocalizedModule/Basic.lean`.
There is no new localization quotient or assumed universal-property
certificate. The comparison uses the actual localization instances,
verified below by transport along explicit linear equivalences.

This unit supplies no adjunction, polynomial-module restriction,
endomorphism-arrow transport, or source sequence-exactness statement or
proof. In particular, Mathlib's existing exactness results motivate reuse
of its functor, but this file makes no new exactness claim for the chosen
functor. Those are separate publication obligations.

## Independent universes and the chosen functor

Let `R : Type u`, `[CommRing R]`, and `S : Submonoid R`. The carrier and
enlargement universes `v` and `w` are independent of each other and of `u`.
Write `κ = max u v w`.

`sourceRaiseFunctor.{u,v,w}` is exactly
`ModuleCat.uliftFunctor.{max u w,v} R`, from `ModuleCat.{v} R` to
`ModuleCat.{κ} R`. Its object at M is the published `raisedSource M`,
with carrier `ULift.{max u w} M`. `sourceRaiseFunctor_obj`,
`sourceRaiseFunctor_map_up` and `sourceRaiseFunctor_map_apply` identify its
objects and its function `ULift.up ∘ f ∘ ULift.down`.

`chosenLocalFunctor.{u,v,w} S` has target `LocalModuleCat.{u,κ} S`.
Its object at M is exactly `canonicalLocalObject.{u,v,w} S M`, with carrier
`ULift.{w} (LocalizedModule S M)` and the published locality proof.
Its map is `chosenLocalMap S f`. `chosenLocalMap_hom` identifies the
underlying R-linear map as

```text
ULift.moduleEquiv.symm ∘
  IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S N) f.hom ∘
  ULift.moduleEquiv.
```

`chosenLocalMap_mk` gives its value on every denominator representative:

```text
ULift.up (LocalizedModule.mk m s) ↦
  ULift.up (LocalizedModule.mk (f m) s).
```

The identity and composition laws `chosenLocalMap_id` and
`chosenLocalMap_comp` follow by induction on localization representatives.
`chosenLocalizationNatTrans` has components precisely the published
`canonicalModuleMap S M`, from the raised source to the underlying chosen
local object. Its naturality proof evaluates on raised elements and uses
the representative formula at denominator one. Thus it works for every
actual R-linear morphism in the source module category.

## The exact Mathlib composite and its actions

`mathlibLocalizationFunctor.{u,v,w} S` is defined to be the composite

```text
sourceRaiseFunctor ⋙ ModuleCat.localizedModuleFunctor.{κ} S ⋙
  ModuleCat.restrictScalars (algebraMap R (Localization S)).
```

The required `Small.{κ} R` is synthesized internally, since κ contains u;
no smallness premise is exposed. Its underlying carrier at M is
`Shrink.{κ} (LocalizedModule S (ULift.{max u w} M))`.
Its R-action is the action obtained by restriction from the
`Localization S`-action. This action is not assumed definitionally equal
to the native R-action on the Shrink carrier.

`mathlibActionEquiv S M` compares those two actions by an R-linear
equivalence whose function and inverse are both the identity. Its
linearity is proved with `IsScalarTower.algebraMap_smul`, which identifies
multiplication by `algebraMap R (Localization S) r` with the native
multiplication by r. Consequently `mathlibCanonicalMap S M` is an
R-linear categorical map into the actual restricted object. Its function,
as recorded by `mathlibCanonicalMap_apply`, is exactly

```text
((sourceRaiseFunctor.obj M).localizedModuleMkLinearMap S).
```

`mathlibCanonicalMap_isLocalizedModule` transports Mathlib's actual
localization instance through `mathlibActionEquiv`. Its `map_units`
property proves `mathlibLocalizationFunctor_isSLocal`, for this restricted
R-action. `mathlibLocalFunctor` is the full-subcategory lift of the same
functor. `mathlibLocalFunctor_inclusion` identifies the whole composite
with inclusion by definitional equality; the object and morphism
identifications are also named separately.

`mathlibLocalizationNatTrans` bundles these specific canonical maps into a
natural transformation from `sourceRaiseFunctor`. Its naturality follows
from `IsLocalizedModule.map_apply` for the actual localized raised map.
The construction therefore compares the specified canonical arrows and
maps, rather than arbitrary objectwise choices.

## The natural comparison and its intrinsic laws

`canonicalModuleMap_isLocalizedModule` verifies that the published chosen
map is a localization of the raised source, by transporting the ordinary
`LocalizedModule.mkLinearMap` through the two `ULift.moduleEquiv` maps.
`chosenMathlibLinearEquiv` is `IsLocalizedModule.linearEquiv` applied to
this instance and the verified Mathlib canonical-map instance. Its
compatibility with the canonical maps is
`chosenMathlibLinearEquiv_canonical`.

`chosenMathlibIsoComponent` lifts this linear equivalence into the actual
full subcategory. `chosenMathlibIsoComponent_naturality` proves its square
for every module morphism: localization extensionality reduces the square
to the raised source, where the two canonical-map naturality equations and
canonical compatibility prove equality. `chosenMathlibIso` bundles the
components into an actual natural isomorphism

```text
chosenLocalFunctor S ≅ mathlibLocalFunctor S.
```

`chosenMathlibIso_canonical` states the required equation

```text
canonicalModuleMap S M ≫
  localModuleInclusion.map ((chosenMathlibIso S).hom.app M) =
    (mathlibLocalizationNatTrans S).app M.
```

`chosenMathlibIso_hom_mk` identifies its function on every representative
with exactly

```text
ULift.up (LocalizedModule.mk m s) ↦
  (Shrink.linearEquiv R
    (LocalizedModule S (ULift.{max u w} M))).symm
      (LocalizedModule.mk (ULift.up m) s).
```

The target is the actual restricted Mathlib module carrier. The proof
cancels multiplication by the denominator using its bijectivity there,
then uses linearity and canonical compatibility. Both natural inverse
laws are recorded by `chosenMathlibIso_hom_inv` and
`chosenMathlibIso_inv_hom` and are part of the constructed natural
isomorphism itself.

Every construction permits the zero ring, zero modules, and arbitrary
submonoids including ones containing zero. There is no nontriviality,
faithfulness, cardinality bound, finite generation, dimension, domain, or
nonzero-denominator hypothesis. The fraction calculation uses invertible
endomorphisms on local modules, so it also applies when the localized
module collapses to zero.

This module retains the independently reviewed universal-property construction.
The explicit transport construction is available in
[RenardLocalModuleFunctor](RenardLocalModuleFunctor.md). The two constructions
keep their own definitions and intrinsic laws.
