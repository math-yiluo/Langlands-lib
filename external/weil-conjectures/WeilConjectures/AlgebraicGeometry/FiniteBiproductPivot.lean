/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts

import Mathlib.Data.Fin.Tuple.Basic

/-! # Assembly of a pivot in a finite biproduct

This is the categorical block-matrix step of the integral pivot construction.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe v u
open CategoryTheory Limits

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

private lemma finitePivot_tail_zero (P : C) {n : ℕ} (j : Fin (n + 1)) :
    biproduct.ι (fun _ : Fin (n + 1) ↦ P) j ≫
      (biproduct.lift fun k : Fin n ↦
        biproduct.π (fun _ : Fin (n + 1) ↦ P) (j.succAbove k)) = 0 := by
  apply biproduct.hom_ext
  intro k
  simp

private lemma finitePivot_tail_succ (P : C) {n : ℕ} (j : Fin (n + 1)) (i : Fin n) :
    biproduct.ι (fun _ : Fin (n + 1) ↦ P) (j.succAbove i) ≫
      (biproduct.lift fun k : Fin n ↦
        biproduct.π (fun _ : Fin (n + 1) ↦ P) (j.succAbove k)) =
      biproduct.ι (fun _ : Fin n ↦ P) i := by
  apply biproduct.hom_ext
  intro k
  by_cases h : i = k
  · subst k; simp
  · simp [h, Fin.succAbove_right_injective.ne h]

variable [HasBinaryBiproducts C]

private noncomputable def finitePivotSplit (P : C) {n : ℕ} (j : Fin (n + 1)) :
    (⨁ fun _ : Fin (n + 1) ↦ P) ≅ P ⊞ (⨁ fun _ : Fin n ↦ P) where
  hom := biprod.lift (biproduct.π (fun _ : Fin (n + 1) ↦ P) j)
    (biproduct.lift fun k ↦ biproduct.π (fun _ : Fin (n + 1) ↦ P) (j.succAbove k))
  inv := biprod.desc (biproduct.ι (fun _ : Fin (n + 1) ↦ P) j)
    (biproduct.desc fun k ↦ biproduct.ι (fun _ : Fin (n + 1) ↦ P) (j.succAbove k))
  hom_inv_id := by
    apply biproduct.hom_ext'
    intro i
    induction i using j.succAboveCases with
    | x => simp [biprod.lift_desc, Preadditive.comp_add, ← Category.assoc,
        finitePivot_tail_zero]
    | p i => simp [biprod.lift_desc, Preadditive.comp_add, ← Category.assoc,
        finitePivot_tail_succ, Fin.succAbove_ne]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext
    · simp
    · apply biproduct.hom_ext
      intro i
      simp
    · apply biproduct.hom_ext'
      intro i
      simp
    · apply biproduct.hom_ext'
      intro i
      apply biproduct.hom_ext
      intro k
      by_cases h : i = k
      · subst k; simp
      · simp [h, Fin.succAbove_right_injective.ne h]

/-- A divisible row gives a pivot block after splitting off its selected summands.

Source: the finite biproduct step in the continuous-function pivot argument for
Bhatt--Scholze, Section 6.8, Proposition 6.8.11(1).
(auxiliary; not a blueprint node)

Proof: split the selected source and target indices from their finite complements.
The other row coefficients factor through the selected coefficient by assumption.
Their biproduct descent is r; the remaining column and square block are obtained by
composing the transformed map with the binary inclusions and projections. Binary
and finite biproduct extensionality verify the four blocks. -/
theorem finiteBiproduct_pivot {P : C} {n t : ℕ}
    (f : (⨁ fun _ : Fin n ↦ P) ⟶ ⨁ fun _ : Fin t ↦ P)
    (i : Fin t) (j : Fin n)
    (q : Fin n → (P ⟶ P))
    (hq : ∀ k, q k ≫ (biproduct.ι (fun _ : Fin n ↦ P) j ≫ f ≫
      biproduct.π (fun _ : Fin t ↦ P) i) =
      biproduct.ι (fun _ : Fin n ↦ P) k ≫ f ≫ biproduct.π (fun _ : Fin t ↦ P) i) :
    ∃ (m s : ℕ), m < n ∧
      ∃ (eA : (⨁ fun _ : Fin n ↦ P) ≅ P ⊞ (⨁ fun _ : Fin m ↦ P))
        (eB : (⨁ fun _ : Fin t ↦ P) ≅ P ⊞ (⨁ fun _ : Fin s ↦ P))
        (r : (⨁ fun _ : Fin m ↦ P) ⟶ P)
        (c : P ⟶ ⨁ fun _ : Fin s ↦ P)
        (d : (⨁ fun _ : Fin m ↦ P) ⟶ ⨁ fun _ : Fin s ↦ P),
        eA.inv ≫ f ≫ eB.hom =
          biprod.lift
            (biprod.desc (biproduct.ι (fun _ : Fin n ↦ P) j ≫ f ≫
      biproduct.π (fun _ : Fin t ↦ P) i)
              (r ≫ (biproduct.ι (fun _ : Fin n ↦ P) j ≫ f ≫
      biproduct.π (fun _ : Fin t ↦ P) i)))
            (biprod.desc c d) := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ m =>
    cases t with
    | zero => exact Fin.elim0 i
    | succ s =>
      let eA := finitePivotSplit P j
      let eB := finitePivotSplit P i
      let b := eA.inv ≫ f ≫ eB.hom
      let r := biproduct.desc fun k ↦ q (j.succAbove k)
      refine ⟨m, s, Nat.lt_succ_self m, eA, eB, r,
        biprod.inl ≫ b ≫ biprod.snd, biprod.inr ≫ b ≫ biprod.snd, ?_⟩
      apply biprod.hom_ext' <;> apply biprod.hom_ext
      · simp [b, eA, eB, finitePivotSplit]
      · simp [b]
      · apply biproduct.hom_ext'
        intro k
        simpa [b, eA, eB, finitePivotSplit, r, Category.assoc] using
          (hq (j.succAbove k)).symm
      · simp [b]

end CategoryTheory.Limits
