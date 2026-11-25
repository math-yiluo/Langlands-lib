/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Multifunctor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Shift.CommShiftTwo

/-! # Formal tensor pasting for base linearity

Source: prop-base-linear.proof.md, paragraphs 1--4 (blueprint: lem-fd-base-linear-pasting).
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace CategoryTheory

section
variable {S A B W : Type*} [Category* S] [Category* A] [Category* B] [Category* W]
  [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory W] [BraidedCategory W]
  (U : S ⥤ A) (V : S ⥤ B) (P : A ⥤ W) [P.Monoidal]
  (Q : B ⥤ W) (R : W ⥤ B) (H : W)

private def baseLinearTensorSwap :
    (curriedTensor W).flip ⋙ (Functor.whiskeringRight _ _ _).obj (tensorRight H) ≅
      (curriedTensor W).flip ⋙ (Functor.whiskeringLeft _ _ _).obj (tensorRight H) :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun X ↦
    α_ X M H ≪≫ whiskerLeftIso X (β_ M H) ≪≫ (α_ X H M).symm) (fun f ↦ by
      dsimp
      simp only [whiskerLeftIso_hom, Category.assoc]
      rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
        associator_inv_naturality_left])) (fun g ↦ by
      ext X
      change (X ◁ g) ▷ H ≫ (α_ X _ H).hom ≫ X ◁ (β_ _ H).hom ≫
          (α_ X H _).inv =
        ((α_ X _ H).hom ≫ X ◁ (β_ _ H).hom ≫ (α_ X H _).inv) ≫ (X ⊗ H) ◁ g
      rw [associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc,
        BraidedCategory.braiding_naturality_left, whiskerLeft_comp_assoc, Category.assoc,
        Category.assoc, associator_inv_naturality_right])

private def baseLinearKernelPreparation (pc : U ⋙ P ≅ V ⋙ Q) :
    U ⋙ (curriedTensor A).flip ⋙
        (Functor.whiskeringRight _ _ _).obj (P ⋙ tensorRight H ⋙ R) ≅
      V ⋙ (Q ⋙ (curriedTensor W).flip ⋙ (Functor.whiskeringRight _ _ _).obj R) ⋙
        (Functor.whiskeringLeft _ _ _).obj (tensorRight H) ⋙
        (Functor.whiskeringLeft _ _ _).obj P := by
  let μ : (curriedTensor A).flip ⋙ (Functor.whiskeringRight _ _ _).obj P ≅
      P ⋙ (curriedTensor W).flip ⋙ (Functor.whiskeringLeft _ _ _).obj P :=
    (flipFunctor _ _ _).mapIso (Functor.curriedTensorPreIsoPost P).symm
  let s₁ := Functor.isoWhiskerLeft U
    (Functor.isoWhiskerRight μ
      ((Functor.whiskeringRight _ _ _).obj (tensorRight H ⋙ R)))
  let s₂ := Functor.isoWhiskerRight pc
    ((curriedTensor W).flip ⋙ (Functor.whiskeringLeft _ _ _).obj P ⋙
      (Functor.whiskeringRight _ _ _).obj (tensorRight H ⋙ R))
  let s₃ := Functor.isoWhiskerLeft (V ⋙ Q)
    (Functor.isoWhiskerRight (baseLinearTensorSwap H)
      ((Functor.whiskeringRight _ _ _).obj R ⋙
        (Functor.whiskeringLeft _ _ _).obj P))
  exact s₁ ≪≫ s₂ ≪≫ s₃

/-- Pasting monoidal pullback, a square compositor, tensor symmetry and projection
is natural in the base variable as well as in the transformed object, on exactly
those full subcategories where the specified projection map is invertible.

Source: prop-base-linear.proof.md, paragraphs 1--4
(blueprint: lem-fd-base-linear-pasting).
Proof: use the inverse tensorator of P, then the square compositor pc on the
second factor. Move this factor past H by associator, braiding and inverse
associator. Restrict the projection transformation to J and V, and invert it
using the component hypotheses. Each constituent is already a natural
transformation, so their composite is natural in both arguments. -/
theorem kernel_base_linear_of_projection
    {I : Type*} [Category* I] (J : I ⥤ A)
    (pc : U ⋙ P ≅ V ⋙ Q)
    (π : curriedTensorInsertFunctor₁ R ⟶
      curriedTensorPost R ⋙ (Functor.whiskeringLeft _ _ _).obj Q)
    (h : ∀ (N : S) (K : I), IsIso ((π.app (P.obj (J.obj K) ⊗ H)).app (V.obj N))) :
    Nonempty (U ⋙ (curriedTensor A).flip ⋙
        (Functor.whiskeringRight _ _ _).obj (P ⋙ tensorRight H ⋙ R) ⋙
        (Functor.whiskeringLeft _ _ _).obj J ≅
      V ⋙ (curriedTensor B).flip ⋙
        (Functor.whiskeringLeft _ _ _).obj (P ⋙ tensorRight H ⋙ R) ⋙
        (Functor.whiskeringLeft _ _ _).obj J) := by
  let t := Functor.whiskerLeft V
    (Functor.whiskerRight ((flipFunctor _ _ _).map π)
      ((Functor.whiskeringLeft _ _ _).obj (tensorRight H) ⋙
        (Functor.whiskeringLeft _ _ _).obj P))
  let t' := Functor.whiskerRight t ((Functor.whiskeringLeft _ _ _).obj J)
  have (N : S) : IsIso (t'.app N) := by
    have (K : I) : IsIso ((t'.app N).app K) := h N K
    exact NatIso.isIso_of_isIso_app _
  have := NatIso.isIso_of_isIso_app t'
  exact ⟨Functor.isoWhiskerRight (baseLinearKernelPreparation U V P Q R H pc)
    ((Functor.whiskeringLeft _ _ _).obj J) ≪≫ (asIso t').symm⟩

/-- A shift after a base-linear functor is still base-linear when right tensor
commutes with the shift naturally in the tensor factor.
Source: prop-base-linear.proof.md, paragraph 4
(blueprint: lem-fd-base-linear-shift).
Proof: whisker the given two-variable comparison with the shift. The remaining
comparison is the shift constraint of right tensor. Its naturality in the base
variable is the shift compatibility of the tensor map. -/
theorem kernel_base_linear_shift
    {I : Type*} [Category* I] (J : I ⥤ A) (F : A ⥤ B)
    [HasShift B ℤ] [Preadditive B] [∀ n : ℤ, (shiftFunctor B n).Additive]
    [(curriedTensor B).CommShift₂Int]
    (e : U ⋙ (curriedTensor A).flip ⋙ (Functor.whiskeringRight _ _ _).obj F ⋙
        (Functor.whiskeringLeft _ _ _).obj J ≅
      V ⋙ (curriedTensor B).flip ⋙ (Functor.whiskeringLeft _ _ _).obj F ⋙
        (Functor.whiskeringLeft _ _ _).obj J) (r : ℤ) :
    Nonempty (U ⋙ (curriedTensor A).flip ⋙
        (Functor.whiskeringRight _ _ _).obj (F ⋙ shiftFunctor B r) ⋙
        (Functor.whiskeringLeft _ _ _).obj J ≅
      V ⋙ (curriedTensor B).flip ⋙
        (Functor.whiskeringLeft _ _ _).obj (F ⋙ shiftFunctor B r) ⋙
        (Functor.whiskeringLeft _ _ _).obj J) := by
  let s : (curriedTensor B).flip ⋙
        (Functor.whiskeringRight _ _ _).obj (shiftFunctor B r) ≅
      (curriedTensor B).flip ⋙
        (Functor.whiskeringLeft _ _ _).obj (shiftFunctor B r) :=
    NatIso.ofComponents (fun L ↦ ((tensorRight L).commShiftIso r).symm) (fun f ↦ by
      ext X
      simpa [Category.assoc] using
        congrArg (fun k ↦ k ≫ ((tensorRight _).commShiftIso r).inv.app X)
          (NatTrans.shift_app ((curriedTensor B).flip.map f) r X))
  exact ⟨Functor.isoWhiskerRight e ((Functor.whiskeringRight _ _ _).obj
      (shiftFunctor B r)) ≪≫
    Functor.isoWhiskerLeft V (Functor.isoWhiskerRight s
      ((Functor.whiskeringLeft _ _ _).obj F ⋙
        (Functor.whiskeringLeft _ _ _).obj J))⟩

end
end CategoryTheory
