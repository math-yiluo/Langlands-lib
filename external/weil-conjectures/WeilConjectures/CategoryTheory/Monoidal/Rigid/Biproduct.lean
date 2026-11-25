/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Dualizable

/-!
# Exact pairings of biproducts

In a monoidal preadditive category, the binary biproduct `X ⊞ Y` of two objects with right duals
is paired with the biproduct `Xᘁ ⊞ Yᘁ` of the duals (`CategoryTheory.exactPairingBiprod`), and a
zero object is paired with itself (`CategoryTheory.exactPairingOfIsZero`). For finite biproducts
see `CategoryTheory.Limits.Bicone.exactPairing`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]

/-- The binary biproduct of two objects with right duals is paired with the biproduct of the
duals. -/
@[instance_reducible]
noncomputable def exactPairingBiprod [HasBinaryBiproducts C] (X Y : C) [HasRightDual X]
    [HasRightDual Y] : ExactPairing (X ⊞ Y) (Xᘁ ⊞ Yᘁ) where
  coevaluation' := η_ X Xᘁ ≫ (biprod.inl ⊗ₘ biprod.inl) + η_ Y Yᘁ ≫ (biprod.inr ⊗ₘ biprod.inr)
  evaluation' := (biprod.fst ⊗ₘ biprod.fst) ≫ ε_ X Xᘁ + (biprod.snd ⊗ₘ biprod.snd) ≫ ε_ Y Yᘁ
  coevaluation_evaluation' := by
    simp only [MonoidalPreadditive.whiskerLeft_add, MonoidalPreadditive.add_whiskerRight,
      Preadditive.add_comp, Preadditive.comp_add, whiskerLeft_coevaluation_evaluation,
      biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd,
      MonoidalCategory.whiskerLeft_id, id_whiskerRight, MonoidalPreadditive.whiskerLeft_zero,
      MonoidalPreadditive.zero_whiskerRight, zero_comp, comp_zero, add_zero, zero_add,
      Category.id_comp, ExactPairing.coevaluation_evaluation_assoc, whiskerRight_id,
      id_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Preadditive.comp_add, ← Category.assoc biprod.fst, ← Category.assoc biprod.snd,
      ← Preadditive.add_comp, biprod.total, Category.id_comp]
  evaluation_coevaluation' := by
    simp only [MonoidalPreadditive.whiskerLeft_add, MonoidalPreadditive.add_whiskerRight,
      Preadditive.add_comp, Preadditive.comp_add, whiskerRight_coevaluation_evaluation,
      biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd,
      MonoidalCategory.whiskerLeft_id, id_whiskerRight, MonoidalPreadditive.whiskerLeft_zero,
      MonoidalPreadditive.zero_whiskerRight, zero_comp, comp_zero, add_zero, zero_add,
      Category.id_comp, ExactPairing.evaluation_coevaluation_assoc, whiskerRight_id,
      id_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Preadditive.comp_add, ← Category.assoc biprod.fst, ← Category.assoc biprod.snd,
      ← Preadditive.add_comp, biprod.total, Category.id_comp]

/-- A zero object is paired with itself, with zero evaluation and coevaluation. -/
@[instance_reducible]
noncomputable def exactPairingOfIsZero {Z : C} (hZ : IsZero Z) : ExactPairing Z Z where
  coevaluation' := 0
  evaluation' := 0
  coevaluation_evaluation' := (hZ.of_iso (ρ_ Z)).eq_of_src _ _
  evaluation_coevaluation' := (hZ.of_iso (λ_ Z)).eq_of_src _ _


end CategoryTheory
