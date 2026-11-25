/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.DirectImageSquareUnitTransport
public import WeilConjectures.AlgebraicGeometry.NormalizedDirectImageCompUnit
/-! # Component assembly for normalized direct-image squares
Source: Stacks Project, Cohomology, Tag 0D5T.
(blueprint: lem-pc-normalized-direct-image-square-unit-component-assembly).
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  DerivedCategory.Qh
private theorem square_paste {C : Type*} [Category C]
    {A₁ A₂ B₁ B₂ P Q : C} (c₁ : A₁ ≅ B₁) (c₂ : A₂ ≅ B₂)
    (u₁ : P ⟶ B₁) (u₂ : Q ⟶ B₂) (b₁ : P ⟶ A₁) (b₂ : Q ⟶ A₂)
    (d : B₁ ⟶ B₂) (e : P ⟶ Q)
    (h₁ : u₁ ≫ c₁.inv = b₁) (h₂ : u₂ ≫ c₂.inv = b₂)
    (he : u₁ ≫ d = e ≫ u₂) :
    b₁ ≫ c₁.hom ≫ d ≫ c₂.inv = e ≫ b₂ := by
  rw [← h₁, ← h₂]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, he, Category.assoc]

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
local instance (Z : Scheme.{u}) : HasDerivedCategory.{w} Z.Modules :=
  inferInstanceAs (HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace)))
local instance (Z : Scheme.{u}) : IsGrothendieckAbelian.{u} Z.Modules :=
  SheafOfModules.isGrothendieckAbelian _
attribute [local instance] instHasKInjectiveResolutionsModules
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.lazyProjDelta false in
set_option backward.isDefEq.lazyWhnfCore false in
set_option linter.all false in
/-- Component assembly from the two comparison-unit equations and transport.
Source: Stacks Project, Cohomology, Tag 0D5T.
(blueprint: lem-pc-normalized-direct-image-square-unit-component-assembly).
-/
theorem normalizedDirectImageSquare_component
    {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (gX : X' ⟶ X)
    (h : gX ≫ f = f' ≫ g)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) (.up ℤ))
    (h₁ : (RingedSpace.moduleDirectImage (gX ≫ f).toLRSHom.toShHom).rightDerivedFunctorUnit.app K ≫
      (schemeNormalizedDirectImageCompIso gX f).inv.app (DerivedCategory.Qh.obj K) =
      (Functor.rightDerivedFunctorCompUnit (Scheme.Modules.pushforward gX)
        (Scheme.Modules.pushforward f)).app K)
    (h₂ : (RingedSpace.moduleDirectImage (f' ≫ g).toLRSHom.toShHom).rightDerivedFunctorUnit.app K ≫
      (schemeNormalizedDirectImageCompIso f' g).inv.app (DerivedCategory.Qh.obj K) =
      (Functor.rightDerivedFunctorCompUnit (Scheme.Modules.pushforward f')
        (Scheme.Modules.pushforward g)).app K)
    (ht : (RingedSpace.moduleDirectImage (gX ≫ f).toLRSHom.toShHom).rightDerivedFunctorUnit.app K ≫
      (eqToHom (congrArg (fun v ↦ schemeDerivedDirectImage v) h)).app
        (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory
          (directImageSquareIso gX f f' g h).hom (.up ℤ)).app K) ≫
        (RingedSpace.moduleDirectImage (f' ≫ g).toLRSHom.toShHom).rightDerivedFunctorUnit.app K) :
    (Functor.rightDerivedFunctorCompUnit (Scheme.Modules.pushforward gX)
      (Scheme.Modules.pushforward f)).app K ≫
      (schemeNormalizedDirectImageCompIso gX f).hom.app (DerivedCategory.Qh.obj K) ≫
      (eqToHom (congrArg (fun v ↦ schemeDerivedDirectImage v) h)).app
        (DerivedCategory.Qh.obj K) ≫
      (schemeNormalizedDirectImageCompIso f' g).inv.app (DerivedCategory.Qh.obj K) =
    DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory
        (Scheme.Modules.pushforwardComp gX f ≪≫ Scheme.Modules.pushforwardCongr h ≪≫
          (Scheme.Modules.pushforwardComp f' g).symm).hom (.up ℤ)).app K) ≫
      (Functor.rightDerivedFunctorCompUnit (Scheme.Modules.pushforward f')
      (Scheme.Modules.pushforward g)).app K := by
  refine square_paste
    ((schemeNormalizedDirectImageCompIso gX f).app (DerivedCategory.Qh.obj K))
    ((schemeNormalizedDirectImageCompIso f' g).app (DerivedCategory.Qh.obj K))
    _ _ _ _ _ _ h₁ h₂ ?_
  simp only [directImageSquareIso] at ht
  exact ht

end AlgebraicGeometry
