/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImageSquareMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Normalization of derived direct-image composition units
Source: Stacks Project, Cohomology, Tag 0D5T.
(blueprint: lem-pc-normalized-direct-image-square-unit-comp-normalization).
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
private theorem compUnit_app {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (K : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit F G).app K =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K) := by
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app
      ((HomotopyCategory.quotient _ _).obj L) = 𝟙 _ := by
    have h := Iso.inv_hom_id_app
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ))
      ((HomotopyCategory.quotient _ _).obj L)
    erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at h
    exact h
  erw [hi, CategoryTheory.Functor.map_id, Category.id_comp]
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
local instance (Z : Scheme.{u}) : HasDerivedCategory.{w} Z.Modules :=
  inferInstanceAs (HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace)))
local instance (Z : Scheme.{u}) : IsGrothendieckAbelian.{u} Z.Modules :=
  SheafOfModules.isGrothendieckAbelian _
local instance (Z : Scheme.{u}) : Abelian.HasKInjectiveResolutions Z.Modules :=
  Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian

private theorem schemeCompUnit_app {A B C : Scheme.{u}} (s : A ⟶ B) (t : B ⟶ C)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings A.toRingedSpace)) (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit (Scheme.Modules.pushforward s)
      (Scheme.Modules.pushforward t)).app K =
    (RingedSpace.moduleDirectImage t.toLRSHom.toShHom).rightDerivedFunctorUnit.app
        (((RingedSpace.moduleDirectImage s.toLRSHom.toShHom).mapHomotopyCategory (.up ℤ)).obj K) ≫
      (RingedSpace.moduleDirectImage t.toLRSHom.toShHom).rightDerivedFunctor.map
        ((RingedSpace.moduleDirectImage s.toLRSHom.toShHom).rightDerivedFunctorUnit.app K) := by
  exact compUnit_app (Scheme.Modules.pushforward s) (Scheme.Modules.pushforward t) K

private theorem schemeNormalizedDirectImageCompIso_eq
    {A B C : Scheme.{u}} (s : A ⟶ B) (t : B ⟶ C) :
    schemeNormalizedDirectImageCompIso s t =
      Classical.choose (RingedSpace.exists_derivedModuleDirectImageComposition
        s.toLRSHom.toShHom t.toLRSHom.toShHom) := rfl

/-- The fixed composition comparison converts the ringed-space unit to the scheme unit.
Source: Stacks Project, Cohomology, Tag 0D5T.
(blueprint: lem-pc-normalized-direct-image-square-unit-comp-normalization).
-/
theorem normalizedDirectImageCompUnit {A B C : Scheme.{u}} (s : A ⟶ B) (t : B ⟶ C)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings A.toRingedSpace)) (.up ℤ)) :
    (RingedSpace.moduleDirectImage (s ≫ t).toLRSHom.toShHom).rightDerivedFunctorUnit.app K ≫
      (schemeNormalizedDirectImageCompIso s t).inv.app (DerivedCategory.Qh.obj K) =
    (Functor.rightDerivedFunctorCompUnit (Scheme.Modules.pushforward s)
      (Scheme.Modules.pushforward t)).app K := by
  -- Focus each rewrite to avoid reducing the derived functors on the other side.
  have hcomp := congrArg (fun e ↦ e.inv.app (DerivedCategory.Qh.obj K))
    (schemeNormalizedDirectImageCompIso_eq (A := A) (B := B) (C := C) s t)
  conv_rhs => rw [schemeCompUnit_app (A := A) (B := B) (C := C) s t K]
  conv_lhs => rw [hcomp]
  exact Classical.choose_spec
    (@RingedSpace.exists_derivedModuleDirectImageComposition.{u, w, w, w}
      A.toRingedSpace B.toRingedSpace C.toRingedSpace
      (‹∀ Z : Scheme.{u}, HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace))› A)
      (‹∀ Z : Scheme.{u}, HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace))› B)
      (‹∀ Z : Scheme.{u}, HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace))› C)
      s.toLRSHom.toShHom t.toLRSHom.toShHom) K

end AlgebraicGeometry
