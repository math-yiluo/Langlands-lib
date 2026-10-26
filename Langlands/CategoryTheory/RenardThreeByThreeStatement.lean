import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Renard's three-by-three bottom-row construction

The statement of Renard 2026, A.VI.2(8), printed page 262 / PDF page 268:
two short exact rows and three short exact columns admit a compatible short
exact bottom row on the three given bottom objects.
-/

universe u v

open CategoryTheory

namespace Langlands.CategoryTheory

/-- The two missing bottom arrows in Renard's three-by-three diagram exist
on the given quotient objects and form a compatible short exact row. -/
def RenardThreeByThreeBottomRowStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ (S₁ S₂ : ShortComplex C) (τ : S₁ ⟶ S₂)
    (Z₁ Z₂ Z₃ : C)
    (p₁ : S₂.X₁ ⟶ Z₁) (p₂ : S₂.X₂ ⟶ Z₂) (p₃ : S₂.X₃ ⟶ Z₃)
    (w₁ : τ.τ₁ ≫ p₁ = 0) (w₂ : τ.τ₂ ≫ p₂ = 0) (w₃ : τ.τ₃ ≫ p₃ = 0),
    S₁.ShortExact →
    S₂.ShortExact →
    (ShortComplex.mk τ.τ₁ p₁ w₁).ShortExact →
    (ShortComplex.mk τ.τ₂ p₂ w₂).ShortExact →
    (ShortComplex.mk τ.τ₃ p₃ w₃).ShortExact →
    ∃ (a : Z₁ ⟶ Z₂) (b : Z₂ ⟶ Z₃) (w : a ≫ b = 0),
      p₁ ≫ a = S₂.f ≫ p₂ ∧
      p₂ ≫ b = S₂.g ≫ p₃ ∧
      (ShortComplex.mk a b w).ShortExact

end Langlands.CategoryTheory
