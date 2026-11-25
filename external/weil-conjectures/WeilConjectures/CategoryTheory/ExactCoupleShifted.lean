/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCouple


public import WeilConjectures.Algebra.Homology.ExactCouple.Basic
public import Mathlib.CategoryTheory.Abelian.Exact

/-! # Shifted-map compatibility view of the canonical upstream exact couple -/

@[expose] public section

universe u v w

namespace CategoryTheory

open Limits



namespace BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C] {s : ℕ}















noncomputable def extendMap {κ : Type w} [AddCommGroup κ]
    (A B : κ → C) (a : κ) (f : ∀ i, A i ⟶ B (i + a))
    (i j : κ) : A i ⟶ B j := by
  classical
  exact if h : i + a = j then f i ≫ eqToHom (congrArg B h) else 0

lemma extendMap_same {κ : Type w} [AddCommGroup κ]
    (A B : κ → C) (a : κ) (f : ∀ i, A i ⟶ B (i + a)) (i : κ) :
    extendMap A B a f i (i + a) = f i := by
  classical
  simp [extendMap]

noncomputable def exactCoupleOfShifted {κ : Type w} [AddCommGroup κ]
    (D E : κ → C) (a b c : κ)
    (α : ∀ i, D i ⟶ D (i + a))
    (f : ∀ i, E i ⟶ D (i + b))
    (g : ∀ i, D i ⟶ E (i + c))
    (hαg : ∀ i, α i ≫ g (i + a) = 0)
    (hgf : ∀ i, g i ≫ f (i + c) = 0)
    (hfα : ∀ i, f i ≫ α (i + b) = 0)
    (eαg : ∀ i, (ShortComplex.mk (α i) (g (i + a)) (hαg i)).Exact)
    (egf : ∀ i, (ShortComplex.mk (g i) (f (i + c)) (hgf i)).Exact)
    (efα : ∀ i, (ShortComplex.mk (f i) (α (i + b)) (hfα i)).Exact) :
    ExactCouple C a b c := by
  classical
  refine { D := D, E := E
           α := extendMap D D a α
           f := extendMap E D b f
           g := extendMap D E c g
           shape_α := ?_, shape_f := ?_, shape_g := ?_
           α_g := ?_, g_f := ?_, f_α := ?_
           exact_α_g := ?_, exact_g_f := ?_, exact_f_α := ?_ }
  · intro i j h; simp [extendMap, h]
  · intro i j h; simp [extendMap, h]
  · intro i j h; simp [extendMap, h]
  · intro i j k
    by_cases hij : i + a = j
    · subst j
      by_cases hjk : i + a + c = k
      · subst k; simpa only [extendMap_same] using hαg i
      · simp [extendMap, hjk]
    · simp [extendMap, hij]
  · intro i j k
    by_cases hij : i + c = j
    · subst j
      by_cases hjk : i + c + b = k
      · subst k; simpa only [extendMap_same] using hgf i
      · simp [extendMap, hjk]
    · simp [extendMap, hij]
  · intro i j k
    by_cases hij : i + b = j
    · subst j
      by_cases hjk : i + b + a = k
      · subst k; simpa only [extendMap_same] using hfα i
      · simp [extendMap, hjk]
    · simp [extendMap, hij]
  · intro i j k hij hjk; subst j; subst k
    simpa only [extendMap_same] using eαg i
  · intro i j k hij hjk; subst j; subst k
    simpa only [extendMap_same] using egf i
  · intro i j k hij hjk; subst j; subst k
    simpa only [extendMap_same] using efα i

/-- Construct a canonical upstream couple from maps supplied only at their shifted indices. -/
noncomputable def ofShifted
    (D E : ℤ → ℤ → C)
    (alpha : ∀ p q, D p q ⟶ D (p - 1) (q + 1))
    (f : ∀ p q, E p q ⟶ D (p + 2) (q - 1))
    (g : ∀ p q, D p q ⟶ E (p + s) (q - s))
    (alpha_f_zero : ∀ p q, f p q ≫ alpha (p + 2) (q - 1) = 0)
    (f_g_zero : ∀ p q, g p q ≫ f (p + s) (q - s) = 0)
    (g_alpha_zero : ∀ p q, alpha p q ≫ g (p - 1) (q + 1) = 0)
    (exact_alpha : ∀ p q,
      imageSubobject (f p q) = kernelSubobject (alpha (p + 2) (q - 1)))
    (exact_f : ∀ p q,
      imageSubobject (g p q) = kernelSubobject (f (p + s) (q - s)))
    (exact_g : ∀ p q,
      imageSubobject (alpha p q) = kernelSubobject (g (p - 1) (q + 1))) :
    BigradedExactCouple C s :=
  { D := D, E := E, alpha := alpha, f := f, g := g
    alpha_f_zero := alpha_f_zero, f_g_zero := f_g_zero, g_alpha_zero := g_alpha_zero
    exact_alpha := exact_alpha, exact_f := exact_f, exact_g := exact_g }

@[simp] lemma ofShifted_D (D E : ℤ → ℤ → C) (alpha f g h₁ h₂ h₃ e₁ e₂ e₃) (p q : ℤ) :
    (ofShifted (s := s) D E alpha f g h₁ h₂ h₃ e₁ e₂ e₃).D p q = D p q := rfl
@[simp] lemma ofShifted_E (D E : ℤ → ℤ → C) (alpha f g h₁ h₂ h₃ e₁ e₂ e₃) (p q : ℤ) :
    (ofShifted (s := s) D E alpha f g h₁ h₂ h₃ e₁ e₂ e₃).E p q = E p q := rfl
@[simp] lemma ofShifted_alpha (D E : ℤ → ℤ → C) (alpha f g h₁ h₂ h₃ e₁ e₂ e₃) (p q : ℤ) :
    (ofShifted (s := s) D E alpha f g h₁ h₂ h₃ e₁ e₂ e₃).alpha p q = alpha p q := by
  rfl
@[simp] lemma ofShifted_f (D E : ℤ → ℤ → C) (alpha f g h₁ h₂ h₃ e₁ e₂ e₃) (p q : ℤ) :
    (ofShifted (s := s) D E alpha f g h₁ h₂ h₃ e₁ e₂ e₃).f p q = f p q := by
  rfl
@[simp] lemma ofShifted_g (D E : ℤ → ℤ → C) (alpha f g h₁ h₂ h₃ e₁ e₂ e₃) (p q : ℤ) :
    (ofShifted (s := s) D E alpha f g h₁ h₂ h₃ e₁ e₂ e₃).g p q = g p q := by
  rfl

end BigradedExactCouple
end CategoryTheory
