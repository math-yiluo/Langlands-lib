/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs

/-!
# Conjugate maps of additive groups

Two maps `φ : A → B` and `ψ : C → D` between additive types are *conjugate* if there are
additive equivalences `e₁ : A ≃+ C` and `e₂ : B ≃+ D` with `e₂ ∘ φ = ψ ∘ e₁`. This is the form
in which comparison statements "the map `φ` is, up to isomorphisms of its source and target,
the map `ψ`" are recorded. Conjugacy is an equivalence relation, and it is preserved by pre- and
postcomposition with additive equivalences.

## Main definitions

- `Function.AddConjugate φ ψ`: `φ` and `ψ` are conjugate.
-/

@[expose] public section

namespace Function

variable {A B C D E F : Type*} [Add A] [Add B] [Add C] [Add D] [Add E] [Add F]

/-- The maps `φ : A → B` and `ψ : C → D` are conjugate: there are additive equivalences
`e₁ : A ≃+ C` and `e₂ : B ≃+ D` with `e₂ (φ x) = ψ (e₁ x)` for all `x`. -/
def AddConjugate (φ : A → B) (ψ : C → D) : Prop :=
  ∃ (e₁ : A ≃+ C) (e₂ : B ≃+ D), ∀ x, e₂ (φ x) = ψ (e₁ x)

namespace AddConjugate

lemma refl (φ : A → B) : AddConjugate φ φ :=
  ⟨AddEquiv.refl A, AddEquiv.refl B, fun _ ↦ rfl⟩

lemma symm {φ : A → B} {ψ : C → D} (h : AddConjugate φ ψ) : AddConjugate ψ φ := by
  obtain ⟨e₁, e₂, h⟩ := h
  refine ⟨e₁.symm, e₂.symm, fun x ↦ ?_⟩
  apply e₂.injective
  rw [AddEquiv.apply_symm_apply, h, AddEquiv.apply_symm_apply]

lemma trans {φ : A → B} {ψ : C → D} {χ : E → F} (h₁ : AddConjugate φ ψ)
    (h₂ : AddConjugate ψ χ) : AddConjugate φ χ := by
  obtain ⟨e₁, e₂, h₁⟩ := h₁
  obtain ⟨e₁', e₂', h₂⟩ := h₂
  exact ⟨e₁.trans e₁', e₂.trans e₂', fun x ↦ by simp [h₁, h₂]⟩

/-- Postcomposition with an additive equivalence preserves conjugacy. -/
lemma comp_left {φ : A → B} {ψ : C → D} (h : AddConjugate φ ψ) (e : D ≃+ E) :
    AddConjugate φ (e ∘ ψ) := by
  obtain ⟨e₁, e₂, h⟩ := h
  exact ⟨e₁, e₂.trans e, fun x ↦ by simp [h]⟩

/-- Precomposition with an additive equivalence preserves conjugacy. -/
lemma comp_right {φ : A → B} {ψ : C → D} (h : AddConjugate φ ψ) (e : E ≃+ C) :
    AddConjugate φ (ψ ∘ e) := by
  obtain ⟨e₁, e₂, h⟩ := h
  exact ⟨e₁.trans e.symm, e₂, fun x ↦ by simp [h]⟩

/-- A map is conjugate to its pre- and postcomposition with additive equivalences. -/
lemma of_eq_comp {φ : A → B} {ψ : C → D} (e₁ : A ≃+ C) (e₂ : B ≃+ D)
    (h : ∀ x, e₂ (φ x) = ψ (e₁ x)) : AddConjugate φ ψ :=
  ⟨e₁, e₂, h⟩

/-- Conjugate maps: if `ψ' ∘ φ = χ' ∘ χ` with `ψ'`, `χ'` equivalences, `φ` and `χ` are
conjugate. -/
lemma of_comp_eq {φ : A → B} {χ : A → D} (ψ' : B ≃+ E) (χ' : D ≃+ E)
    (h : ∀ x, ψ' (φ x) = χ' (χ x)) : AddConjugate φ χ :=
  ⟨AddEquiv.refl A, ψ'.trans χ'.symm, fun x ↦ by
    simp only [AddEquiv.trans_apply, h, AddEquiv.symm_apply_apply, AddEquiv.refl_apply]⟩

end AddConjugate

end Function
