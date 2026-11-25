/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Tactic.NoncommRing

/-!
# Splitting of idempotents

Supplements to `Mathlib.CategoryTheory.Idempotents.Basic`: splittings of idempotents are
transported along isomorphisms and functors, and in a preadditive category two idempotents
whose difference has square zero are conjugate, so that one splits if and only if the other does.

## Main statements

- `CategoryTheory.Idempotents.exists_split_of_sub_comp_sub_eq_zero`: if `p` and `q` are
  idempotents of an object of a preadditive category with `(p - q) ≫ (p - q) = 0` and `q`
  splits, then `p` splits.
-/

@[expose] public section

namespace CategoryTheory.Idempotents

open Category

variable {C : Type*} [Category* C]

/-- The property that an endomorphism `p` of `X` is split: `p = e ≫ i` for a retraction
`e : X ⟶ Y` and a section `i : Y ⟶ X` with `i ≫ e = 𝟙 Y`. -/
def IsSplit {X : C} (p : X ⟶ X) : Prop :=
  ∃ (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p

lemma isIdempotentComplete_iff_isSplit :
    IsIdempotentComplete C ↔ ∀ (X : C) (p : X ⟶ X), p ≫ p = p → IsSplit p :=
  ⟨fun h ↦ h.idempotents_split, fun h ↦ ⟨h⟩⟩

/-- A splitting is transported along a conjugation by an isomorphism. -/
lemma IsSplit.of_iso {X X' : C} {p : X ⟶ X} {p' : X' ⟶ X'} (f : X ≅ X')
    (hf : p ≫ f.hom = f.hom ≫ p') (h : IsSplit p') : IsSplit p := by
  obtain ⟨Y, i, e, h₁, h₂⟩ := h
  refine ⟨Y, i ≫ f.inv, f.hom ≫ e, by simp [h₁], ?_⟩
  rw [assoc, reassoc_of% h₂, ← reassoc_of% hf, Iso.hom_inv_id, comp_id]

/-- A functor maps split endomorphisms to split endomorphisms. -/
lemma IsSplit.map {D : Type*} [Category* D] (F : C ⥤ D) {X : C} {p : X ⟶ X} (h : IsSplit p) :
    IsSplit (F.map p) := by
  obtain ⟨Y, i, e, h₁, h₂⟩ := h
  exact ⟨F.obj Y, F.map i, F.map e, by rw [← F.map_comp, h₁, F.map_id], by rw [← F.map_comp, h₂]⟩

section Preadditive

variable [Preadditive C]

open Preadditive

/-- If `p` and `q` are idempotents of `X` whose difference has square zero, then
`u = p ≫ q + (𝟙 X - p) ≫ (𝟙 X - q)` is an automorphism of `X` conjugating `q` to `p`. -/
lemma exists_iso_conj_of_sub_comp_sub_eq_zero {X : C} {p q : X ⟶ X} (hp : p ≫ p = p)
    (hq : q ≫ q = q) (hpq : (p - q) ≫ (p - q) = 0) :
    ∃ (u : X ≅ X), q ≫ u.hom = u.hom ≫ p := by
  -- `p ≫ q + q ≫ p = p + q`, from which `q ≫ p ≫ q = q` and `p ≫ q ≫ p = p`.
  have h₁ : p ≫ q + q ≫ p = p + q := by
    have := hpq
    simp only [comp_sub, sub_comp, hp, hq] at this
    rw [← sub_eq_zero, show p ≫ q + q ≫ p - (p + q) = -(p - q ≫ p - (p ≫ q - q)) by abel, this,
      neg_zero]
  have h₂ : p ≫ q ≫ p = p := by
    have := congrArg (fun x ↦ p ≫ x) h₁
    simp only [comp_add, ← assoc, hp] at this
    simp only [assoc] at this
    exact add_left_cancel (this.trans (add_comm _ _))
  have h₃ : q ≫ p ≫ q = q := by
    have := congrArg (fun x ↦ q ≫ x) h₁
    simp only [comp_add, ← assoc, hq] at this
    simp only [assoc] at this
    exact add_right_cancel (this.trans (add_comm _ _))
  refine ⟨⟨q ≫ p + (𝟙 X - q) ≫ (𝟙 X - p), p ≫ q + (𝟙 X - p) ≫ (𝟙 X - q), ?_, ?_⟩, ?_⟩
  · simp only [add_comp, comp_add, sub_comp, comp_sub, assoc, id_comp, comp_id, hp, hq,
      reassoc_of% hp, h₃]
    have := h₁
    rw [← sub_eq_zero] at this ⊢
    rw [← this]
    abel
  · simp only [add_comp, comp_add, sub_comp, comp_sub, assoc, id_comp, comp_id, hp, hq,
      reassoc_of% hq, h₂]
    have := h₁
    rw [← sub_eq_zero] at this ⊢
    rw [← this]
    abel
  · simp [comp_add, add_comp, comp_sub, sub_comp, reassoc_of% hq, hp, hq]

/-- If `p` and `q` are idempotents of `X` whose difference has square zero and `q` splits, then
`p` splits. -/
lemma exists_split_of_sub_comp_sub_eq_zero {X : C} {p q : X ⟶ X} (hp : p ≫ p = p)
    (hq : q ≫ q = q) (hpq : (p - q) ≫ (p - q) = 0) (h : IsSplit q) : IsSplit p := by
  obtain ⟨u, hu⟩ := exists_iso_conj_of_sub_comp_sub_eq_zero hp hq hpq
  exact h.of_iso u.symm (by rw [Iso.symm_hom, ← cancel_epi u.hom, ← reassoc_of% hu,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, comp_id])

end Preadditive

end CategoryTheory.Idempotents
