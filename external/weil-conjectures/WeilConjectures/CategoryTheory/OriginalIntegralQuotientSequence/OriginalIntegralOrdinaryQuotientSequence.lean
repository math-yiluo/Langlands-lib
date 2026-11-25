/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # The canonical ordinary positive quotient Roos sequence

Source: Bhatt--Scholze, Proposition 3.1.10, and the ordinary quotient
reconstruction in the integral closed-exchange argument.
(blueprint: def-sp-original-integral-ordinary-quotient-sequence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe v w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.OriginalIntegralQuotientSequence
variable {A : Type v} [Category.{w} A] [Abelian A]

/-- The identity-induced ordinary quotient transition.
Source: the positive quotient tower, integral closed exchange.
(blueprint: def-sp-original-integral-ordinary-quotient-sequence). -/
def transition (ell n : ℕ) (M : A) :
    cokernel (ell ^ (n + 1 + 1) • 𝟙 M) ⟶ cokernel (ell ^ (n + 1) • 𝟙 M) :=
  cokernel.desc _ (cokernel.π (ell ^ (n + 1) • 𝟙 M)) (by
    have hp : ell ^ (n + 1 + 1) • 𝟙 M = ell • (ell ^ (n + 1) • 𝟙 M) := by
      rw [← mul_nsmul, pow_succ, Nat.mul_comm]
    rw [hp, Preadditive.nsmul_comp, cokernel.condition, smul_zero])

/-- Quotient projections commute with the canonical transition.
Source: the cokernel universal property.
(blueprint: def-sp-original-integral-ordinary-quotient-sequence). -/
@[reassoc (attr := simp)] theorem projection_transition (ell n : ℕ) (M : A) :
    cokernel.π (ell ^ (n + 1 + 1) • 𝟙 M) ≫ transition ell n M =
      cokernel.π (ell ^ (n + 1) • 𝟙 M) :=
  cokernel.π_desc _ _ _

/-- A positive quotient is killed by its defining scalar.
Source: the cokernel relation.
(blueprint: def-sp-original-integral-ordinary-quotient-sequence). -/
theorem quotient_annihilated (ell n : ℕ) (M : A) :
    ell ^ (n + 1) • 𝟙 (cokernel (ell ^ (n + 1) • 𝟙 M)) = 0 := by
  apply (cancel_epi (cokernel.π (ell ^ (n + 1) • 𝟙 M))).1
  simpa only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
    Category.comp_id, Category.id_comp, comp_zero] using
    cokernel.condition (ell ^ (n + 1) • 𝟙 M)

variable [HasLimitsOfShape (Discrete ℕ) A]

/-- The product of the ordinary quotient projections.
Source: Bhatt--Scholze, Proposition 3.1.10.
(blueprint: def-sp-original-integral-ordinary-quotient-sequence). -/
def augmentation (ell : ℕ) (M : A) :
    M ⟶ ∏ᶜ (fun n : ℕ ↦ cokernel (ell ^ (n + 1) • 𝟙 M)) :=
  Pi.lift fun n ↦ cokernel.π (ell ^ (n + 1) • 𝟙 M)

/-- Shift along the actual ordinary quotient transitions.
Source: Bhatt--Scholze, Proposition 3.1.10.
(blueprint: def-sp-original-integral-ordinary-quotient-sequence). -/
def shift (ell : ℕ) (M : A) :
    (∏ᶜ (fun n : ℕ ↦ cokernel (ell ^ (n + 1) • 𝟙 M))) ⟶
      ∏ᶜ (fun n : ℕ ↦ cokernel (ell ^ (n + 1) • 𝟙 M)) :=
  Pi.lift fun n ↦ Pi.π _ (n + 1) ≫ transition ell n M

/-- The augmentation lands in the kernel of one minus transition shift.
Source: compatible quotient projections and product extensionality.
(blueprint: def-sp-original-integral-ordinary-quotient-sequence). -/
theorem augmentation_comp_one_sub (ell : ℕ) (M : A) :
    augmentation ell M ≫ (𝟙 _ - shift ell M) = 0 := by
  apply Pi.hom_ext
  intro n
  simp [augmentation, shift, Preadditive.comp_sub, Preadditive.sub_comp,
    Category.assoc]

/-- The canonical Roos short complex of the ordinary positive quotients.
Source: Bhatt--Scholze, Proposition 3.1.10. Its maps are constructed before any
completeness assertion; the first quotient is at exponent one, including for
ell = 0 or ell = 1.
(blueprint: def-sp-original-integral-ordinary-quotient-sequence). -/
def sequence (ell : ℕ) (M : A) : ShortComplex A :=
  ShortComplex.mk (augmentation ell M) (𝟙 _ - shift ell M)
    (augmentation_comp_one_sub ell M)

end CategoryTheory.OriginalIntegralQuotientSequence
