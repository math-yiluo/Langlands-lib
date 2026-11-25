/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Presheaf
public import WeilConjectures.Mathlib.Topology.Category.TopCat.Opens

/-!
# The pullback of `𝒪`-modules is monoidal

Let `f : X ⟶ Y` be a morphism of schemes. The pullback functor
`AlgebraicGeometry.Scheme.Modules.pullback f : Y.Modules ⥤ X.Modules` is monoidal: it sends
the structure sheaf to the structure sheaf, and the tensor product of two `𝒪ᵧ`-modules to the
tensor product of their pullbacks.

## Main declarations

- `AlgebraicGeometry.Scheme.Modules.pullbackMonoidal`: the pullback functor
  `AlgebraicGeometry.Scheme.Modules.pullback f` is monoidal (an instance).

## Implementation details

This is reduced to the same statement for presheaves of modules,
`PresheafOfModules.pullbackMonoidal`, via the universal property of the category of sheaves of
modules as a localization of presheaves of modules
(`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp`): the pullback of sheaves of
modules lifts the pullback of presheaves of modules followed by sheafification
(`SheafOfModules.sheafificationCompPullback`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The pullback of presheaves of modules along `f` followed by the sheafification is
monoidal. -/
@[instance_reducible]
noncomputable def presheafPullbackCompSheafificationMonoidal :
    (_root_.PresheafOfModules.pullbackOfCommRingCat f.toRingCatPresheafHom ⋙
      sheafification X).Monoidal :=
  @Functor.Monoidal.instComp _ _ _ _ _ _ _ _ _
    (_root_.PresheafOfModules.pullbackOfCommRingCat f.toRingCatPresheafHom) (sheafification X)
    inferInstance (sheafificationMonoidal X)

attribute [local instance] presheafPullbackCompSheafificationMonoidal

/-- The sheafification functor of `X` is a localization functor. Instance search does not
find this instance for the structure sheaf of a scheme. -/
instance (X : Scheme.{u}) : (sheafification X).IsLocalization
    ((Opens.grothendieckTopology X).W.inverseImage
      (_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj)) :=
  inferInstanceAs
    ((_root_.PresheafOfModules.sheafification.{u} (𝟙 X.ringCatSheaf.obj)).IsLocalization
      ((Opens.grothendieckTopology X).W.inverseImage
        (_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj)))

/-- The pullback of sheaves of modules along `f` lifts, along the sheafification functor, the
pullback of presheaves of modules followed by the sheafification. -/
noncomputable instance :
    Localization.Lifting (sheafification Y)
      ((Opens.grothendieckTopology Y).W.inverseImage
        (_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.obj))
      (_root_.PresheafOfModules.pullbackOfCommRingCat f.toRingCatPresheafHom ⋙
        sheafification X)
      (pullback f) :=
  ⟨SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom⟩

/-- **The pullback of `𝒪`-modules is monoidal**: `f^* 𝒪_Y ≅ 𝒪_X` and
`f^* (M ⊗ N) ≅ f^* M ⊗ f^* N`, naturally and compatibly with the associators and unitors.
The comparison maps are
```
δ M N : f^*(M ⊗ N) ⟶ f^*M ⊗ f^*N        η : f^* 𝒪_Y ⟶ 𝒪_X
```
both isomorphisms. -/
noncomputable instance pullbackMonoidal : (pullback f).Monoidal :=
  @Localization.Monoidal.functorMonoidalOfComp _ _ _ _ _ _ (presheafMonoidalCategory Y) _ _
    (sheafification Y)
    ((Opens.grothendieckTopology Y).W.inverseImage
      (_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.obj)) _ (sheafificationMonoidal Y)
    (pullback f)
    (_root_.PresheafOfModules.pullbackOfCommRingCat f.toRingCatPresheafHom ⋙ sheafification X)
    (presheafPullbackCompSheafificationMonoidal f) _ _

end AlgebraicGeometry.Scheme.Modules
