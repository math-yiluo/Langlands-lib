/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Naturality and shifts of inverse-scalar adjunction legs

Source: Stacks Project, Derived Categories, Tags 05RU and 015F.
(blueprint: lem-weil-pbc-scalar-localization-telescope-leg-laws)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe v uD vD uT vT

open CategoryTheory

namespace CategoryTheory

/-- Inverse-scalar adjunction legs are natural and respect coherent shifts.
Source: Stacks Project, Derived Categories, Tags 05RU and 015F.
(blueprint: lem-weil-pbc-scalar-localization-telescope-leg-laws).
Proof: central scalars commute with every morphism in the target. Combine this
with naturality of the adjunction unit. For shifts use linearity of the target
shift, naturality of the two shift comparisons, and compatibility of the unit.
The hypotheses on the unit and on linear shifts are essential. -/
theorem scalarLocalizationTelescopeLegLaws
    (A : Type v) [CommRing A] (t : A)
    {D : Type uD} [Category.{vD} D] [HasShift D ℤ]
    {T : Type uT} [Category.{vT} T] [Preadditive T] [HasShift T ℤ]
    [Linear (Localization.Away t) T]
    [∀ k : ℤ, (shiftFunctor T k).Linear (Localization.Away t)]
    (F : D ⥤ T) [F.CommShift ℤ] (U : T ⥤ D) [U.CommShift ℤ]
    (adj : F ⊣ U) [adj.CommShift ℤ] :
    (∀ (K L : D) (f : K ⟶ L) (n : ℕ),
      f ≫ (adj.unit.app L ≫ U.map
        (((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) •
          𝟙 (F.obj L))) =
      (adj.unit.app K ≫ U.map
        (((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) •
          𝟙 (F.obj K))) ≫ U.map (F.map f)) ∧
    (∀ (L : D) (n : ℕ) (k : ℤ),
      (adj.unit.app (L⟦k⟧) ≫ U.map
        (((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) •
          𝟙 (F.obj (L⟦k⟧)))) ≫
          ((F ⋙ U).commShiftIso k).hom.app L =
      (adj.unit.app L ≫ U.map
        (((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) •
          𝟙 (F.obj L)))⟦k⟧') := by
  constructor
  · intro K L f n
    rw [← Category.assoc, show f ≫ adj.unit.app L =
      adj.unit.app K ≫ U.map (F.map f) from adj.unit.naturality f]
    simp only [Category.assoc, ← U.map_comp,
      Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]
  · intro L n k
    let r : Localization.Away t := IsLocalization.Away.invSelf t ^ n
    have hr : U.map (r • 𝟙 (F.obj (L⟦k⟧))) ≫
        ((F ⋙ U).commShiftIso k).hom.app L =
        ((F ⋙ U).commShiftIso k).hom.app L ≫
          (U.map (r • 𝟙 (F.obj L)))⟦k⟧' := by
      rw [Functor.commShiftIso_comp_hom_app]
      simp only [← Category.assoc, ← U.map_comp, Linear.smul_comp, Category.id_comp]
      rw [show r • (F.commShiftIso k).hom.app L =
          (F.commShiftIso k).hom.app L ≫ (r • 𝟙 (F.obj L))⟦k⟧' by
        simp [Functor.map_smul, Linear.comp_smul]]
      rw [U.map_comp, Category.assoc, U.commShiftIso_hom_naturality]
      simp only [Category.assoc]
    change (adj.unit.app (L⟦k⟧) ≫ U.map (r • 𝟙 _)) ≫ _ =
      (adj.unit.app L ≫ U.map (r • 𝟙 _))⟦k⟧'
    rw [Category.assoc, hr, ← Category.assoc, adj.unit_app_commShiftIso_hom_app,
      Functor.map_comp]

end CategoryTheory
