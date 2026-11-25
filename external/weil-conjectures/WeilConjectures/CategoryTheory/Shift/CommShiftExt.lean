/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Group.Int.Defs

/-! # Uniqueness of shift commutations

A commutation of a functor with shifts is determined by its isomorphisms; for the
`ℤ`-shift it is determined by its component at one, and it is determined by
compatibility with a natural isomorphism.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Two commutations of a functor with a shift agree when all their isomorphisms agree. -/
theorem commShift_ext {A : Type*} [AddMonoid A] [HasShift C A] [HasShift D A] {F : C ⥤ D}
    (c₁ c₂ : F.CommShift A)
    (h : ∀ a : A, @commShiftIso _ _ _ _ F A _ _ _ c₁ a = @commShiftIso _ _ _ _ F A _ _ _ c₂ a) :
    c₁ = c₂ := by
  obtain ⟨i₁, _, _⟩ := c₁
  obtain ⟨i₂, _, _⟩ := c₂
  obtain rfl : i₁ = i₂ := funext h
  rfl

/-- A commutation of a functor with the `ℤ`-shift is determined by its component at one. -/
theorem commShift_ext_of_one [HasShift C ℤ] [HasShift D ℤ] {F : C ⥤ D}
    (c₁ c₂ : F.CommShift ℤ)
    (h : ∀ X : C, (@commShiftIso _ _ _ _ F ℤ _ _ _ c₁ 1).hom.app X =
      (@commShiftIso _ _ _ _ F ℤ _ _ _ c₂ 1).hom.app X) :
    c₁ = c₂ := by
  have h₁ : @commShiftIso _ _ _ _ F ℤ _ _ _ c₁ 1 = @commShiftIso _ _ _ _ F ℤ _ _ _ c₂ 1 := by
    ext X
    exact h X
  apply commShift_ext
  intro n
  induction n using Int.induction_on with
  | zero => rw [@commShiftIso_zero _ _ _ _ F ℤ _ _ _ c₁, @commShiftIso_zero _ _ _ _ F ℤ _ _ _ c₂]
  | succ n ih =>
    rw [@commShiftIso_add _ _ _ _ F ℤ _ _ _ c₁, @commShiftIso_add _ _ _ _ F ℤ _ _ _ c₂, ih, h₁]
  | pred n ih =>
    have hc : -(n : ℤ) - 1 + 1 = -(n : ℤ) := by omega
    have e₁ := @commShiftIso_add' _ _ _ _ F ℤ _ _ _ c₁ _ _ _ hc
    have e₂ := @commShiftIso_add' _ _ _ _ F ℤ _ _ _ c₂ _ _ _ hc
    rw [ih, e₂, h₁] at e₁
    ext X
    have hX := congrArg (fun e ↦ e.hom.app X) e₁
    simp only [CommShift.isoAdd'_hom_app, cancel_epi, cancel_mono] at hX
    exact (shiftFunctor D (1 : ℤ)).map_injective hX.symm

/-- A commutation with shifts making a natural isomorphism compatible is unique. -/
theorem commShift_ext_of_iso {A : Type*} [AddMonoid A] [HasShift C A] [HasShift D A]
    {F G : C ⥤ D} (e : F ≅ G) [F.CommShift A] (c₁ c₂ : G.CommShift A)
    (h₁ : @NatTrans.CommShift _ _ _ _ _ _ e.hom A _ _ _ _ c₁)
    (h₂ : @NatTrans.CommShift _ _ _ _ _ _ e.hom A _ _ _ _ c₂) :
    c₁ = c₂ := by
  apply commShift_ext
  intro a
  ext X
  have k₁ := @NatTrans.shift_app_comm _ _ _ _ _ _ e.hom A _ _ _ _ c₁ h₁ a X
  have k₂ := @NatTrans.shift_app_comm _ _ _ _ _ _ e.hom A _ _ _ _ c₂ h₂ a X
  exact (cancel_epi (e.hom.app _)).1 (k₁.symm.trans k₂)

end CategoryTheory.Functor
