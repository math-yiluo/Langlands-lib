/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.LocalCoefficientLocalization

/-! # The countable multiplication difference

Source: Stacks Project, algebraization.tex, Tag 0997.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- The functor taking a countable power.
Source: Stacks Tag 0997 (auxiliary; not a blueprint node). -/
def countablePower (B : Type u) [Category.{v} B] [HasCountableProducts B] : B ⥤ B where
  obj M := ∏ᶜ fun _ : ℕ ↦ M
  map g := Limits.Pi.map (fun _ : ℕ ↦ g)
  map_id M := by simp
  map_comp g h := by simp [Limits.Pi.map_comp_map]

private def countablePowerIsoLim (B : Type u) [Category.{v} B]
    [HasCountableProducts B] :
    countablePower B ≅ Functor.const (Discrete ℕ) ⋙ (lim : (Discrete ℕ ⥤ B) ⥤ B) :=
  NatIso.ofComponents (fun M ↦ Pi.isoLimit ((Functor.const (Discrete ℕ)).obj M))
    (by
      intro M N g
      apply limit.hom_ext
      rintro ⟨n⟩
      simp [countablePower])

/-- Powers act additively on morphisms.
Source: Stacks Tag 0997 (auxiliary; not a blueprint node). -/
instance countablePower_additive (B : Type u) [Category.{v} B] [Preadditive B]
    [HasCountableProducts B] : (countablePower B).Additive where
  map_add := by intros; apply Pi.hom_ext; intro n; simp [countablePower]

/-- Countable powers commute with limits.
Source: Stacks Tag 0997 (auxiliary; not a blueprint node). -/
instance countablePower_preservesLimitsOfShape (B : Type u) [Category.{v} B]
    [HasCountableProducts B] (D : Type*) [Category* D] [HasLimitsOfShape D B] :
    PreservesLimitsOfShape D (countablePower B) := by
  have : PreservesLimitsOfShape D
      (Functor.const (Discrete ℕ) ⋙ (lim : (Discrete ℕ ⥤ B) ⥤ B)) := inferInstance
  exact preservesLimitsOfShape_of_natIso (countablePowerIsoLim B).symm

/-- Identity minus the multiplication shift on a countable power.
Source: Stacks Tag 0997 (auxiliary; not a blueprint node). -/
def multiplicationDifference {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (U : C) (f : O.obj.obj (op U)) :
    countablePower (SheafOfModules.{u} ((localCoefficientRings O).over U)) ⟶
      countablePower (SheafOfModules.{u} ((localCoefficientRings O).over U)) where
  app M := towerTransitionEndomorphism (K := fun _ : ℕ ↦ M)
    (fun _ ↦ localSectionMultiplication O U f M)
  naturality {_ _} g := towerTransitionEndomorphism_natural_backward _ _ (fun _ ↦ g)
    (fun _ ↦ localSectionMultiplication_naturality O U f g)

end CategoryTheory
