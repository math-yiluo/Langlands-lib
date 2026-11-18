import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-! # Polynomial relations for orthogonal compact rotation generators -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Archimedean.RealCompactPolynomialRelations

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- The monic central-factorial polynomial evaluated at a compact generator. -/
def factor (X : A) : ℕ → A
  | 0 => 1
  | 1 => X
  | n + 2 => (X * X) * factor X n + ((n + 1 : ℂ) ^ 2) • factor X n

variable {X Y Z : A}

omit [Algebra ℂ A] in
/-- The first nontrivial compact polynomial braid relation. -/
theorem braid_one_one
    (hXY : X * Y - Y * X = Z)
    (hZX : Z * X - X * Z = Y)
    (hZY : Z * Y - Y * Z = -X) :
    X * (Y * Y + 1) * X = Y * (X * X + 1) * Y := by
  linear_combination (norm := noncomm_ring)
    hXY * Y * X - Y * X * hXY + hZY * X + Y * hZX

private theorem recurrence_step (t : ℂ)
    (hXY : X * Y - Y * X = Z)
    (hZX : Z * X - X * Z = Y) :
    (X * X + algebraMap ℂ A ((t + 1) ^ 2)) * (Y * X + t • Z) =
      (Y * X + (t + 2) • Z) * (X * X + algebraMap ℂ A (t ^ 2)) := by
  have h1 : X * X * Y - Y * X * X = X * Z + Z * X := by
    linear_combination (norm := noncomm_ring) X * hXY + hXY * X
  have h2 : X * X * Z - Z * X * X = -(X * Y + Y * X) := by
    linear_combination (norm := noncomm_ring) -X * hZX - hZX * X
  have h3 : X * Z * X = X * X * Z + X * Y := by
    linear_combination (norm := noncomm_ring) X * hZX
  simp only [add_mul, mul_add, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
    mul_smul_comm, one_mul, mul_one]
  linear_combination (norm := (noncomm_ring; module))
    h1 * X + (t + 1) • h2 + h3 - t • hXY

theorem factor_add_two (X : A) (n : ℕ) :
    factor X (n + 2) =
      (X * X + algebraMap ℂ A ((n + 1 : ℂ) ^ 2)) * factor X n := by
  simp [factor, add_mul, Algebra.algebraMap_eq_smul_one]

/-- A compact central-factorial operator has an exact first-order shift relation. -/
theorem factor_next_mul
    (hXY : X * Y - Y * X = Z)
    (hZX : Z * X - X * Z = Y) (n : ℕ) :
    factor X (n + 1) * Y = (Y * X + (n + 1 : ℂ) • Z) * factor X n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      simp only [factor, Nat.cast_zero, zero_add, one_smul, mul_one]
      linear_combination (norm := noncomm_ring) hXY
  | one =>
      norm_num [factor]
      linear_combination (norm := (noncomm_ring; module)) X * hXY + hXY * X - hZX
  | more n ih _ =>
      rw [show n + 2 + 1 = (n + 1) + 2 by omega, factor_add_two,
        mul_assoc, ih, ← mul_assoc]
      have hs := recurrence_step (X := X) (Y := Y) (Z := Z) (n + 1 : ℂ) hXY hZX
      have hc : (n + 1 : ℂ) + 2 = (n + 2 : ℂ) + 1 := by ring
      rw [hc] at hs
      simp only [Nat.cast_add, Nat.cast_one] at ⊢
      rw [hs, mul_assoc]
      congr 1
      exact (factor_add_two X n).symm

end Langlands.Archimedean.RealCompactPolynomialRelations

namespace Langlands.Archimedean

/-- Central-factorial compact operators satisfy the first-order shift relation and
its first polynomial braid consequence under the stated orthogonal commutators. -/
def RealCompactPolynomialRelationsStatement : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (X Y Z : A),
    X * Y - Y * X = Z → Z * X - X * Z = Y → Z * Y - Y * Z = -X →
      (∀ n : ℕ, RealCompactPolynomialRelations.factor X (n + 1) * Y =
        (Y * X + (n + 1 : ℂ) • Z) * RealCompactPolynomialRelations.factor X n) ∧
      X * (Y * Y + 1) * X = Y * (X * X + 1) * Y

theorem realCompactPolynomialRelations : RealCompactPolynomialRelationsStatement := by
  intro A _ _ X Y Z hXY hZX hZY
  exact ⟨RealCompactPolynomialRelations.factor_next_mul hXY hZX,
    RealCompactPolynomialRelations.braid_one_one hXY hZX hZY⟩

end Langlands.Archimedean
