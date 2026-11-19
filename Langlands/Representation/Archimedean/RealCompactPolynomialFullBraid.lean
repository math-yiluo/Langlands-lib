import Langlands.Representation.Archimedean.RealCompactPolynomialBraid

/-! # The full compact polynomial braid and recursive corner normal forms -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Archimedean.RealCompactPolynomialFullBraid

open RealCompactPolynomialRelations RealCompactPolynomialBraid

variable {A : Type*} [Ring A] [Algebra ℂ A]

def corner (X Y Z : A) (t : ℂ) : A := Y * X + t • Z

def normalLeft (X Y Z : A) : ℕ → ℂ → A
  | 0, _ => 1
  | 1, t => corner X Y Z (t + 1)
  | a + 2, t =>
      (corner X Y Z (t + 1) * corner X Y Z (t + 2) +
        ((a + 1 : ℂ) ^ 2) • (Y * Y + algebraMap ℂ A ((t + 1) ^ 2))) *
          normalLeft X Y Z a (t + 2)

def normalRight (X Y Z : A) : ℕ → ℂ → A
  | 0, _ => 1
  | 1, t => corner X Y Z (t + 1)
  | a + 2, t =>
      normalRight X Y Z a (t + 2) *
        (corner X Y Z (t + 2) * corner X Y Z (t + 1) +
          ((a + 1 : ℂ) ^ 2) • (X * X + algebraMap ℂ A ((t + 1) ^ 2)))

private theorem factor_commutes (X : A) (n : ℕ) : factor X n * X = X * factor X n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [factor]
  | one => rfl
  | more n ih _ =>
      simp only [factor, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_assoc, ih]

private theorem factor_right_add_two (X : A) (n : ℕ) :
    factor X (n + 2) = factor X n *
      (X * X + algebraMap ℂ A ((n + 1 : ℂ) ^ 2)) := by
  rw [factor_add_two]
  simp only [add_mul, mul_add, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rw [mul_assoc, ← factor_commutes, ← mul_assoc, ← factor_commutes]
  simp only [mul_assoc]

variable {X Y Z : A}

private theorem left_shift
    (hXY : X * Y - Y * X = Z) (hZY : Z * Y - Y * Z = -X) (n : ℕ) :
    X * factor Y (n + 1) = factor Y n * corner X Y Z (n + 1) := by
  have hYX : Y * X - X * Y = -Z := by
    linear_combination (norm := noncomm_ring) -hXY
  have hZY' : (-Z) * Y - Y * (-Z) = X := by
    linear_combination (norm := noncomm_ring) -hZY
  simpa only [corner, smul_neg, sub_neg_eq_add] using mul_factor_next hYX hZY' n

private theorem left_square
    (hXY : X * Y - Y * X = Z) (hZY : Z * Y - Y * Z = -X) (n : ℕ) :
    (X * X) * factor Y (n + 2) =
      factor Y n * (corner X Y Z (n + 1) * corner X Y Z (n + 2)) := by
  have hl2 : X * factor Y (n + 2) =
      factor Y (n + 1) * corner X Y Z (n + 2) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      left_shift hXY hZY (n + 1)
  rw [mul_assoc, hl2, ← mul_assoc, left_shift hXY hZY n, mul_assoc]

private theorem right_square
    (hXY : X * Y - Y * X = Z) (hZX : Z * X - X * Z = Y) (n : ℕ) :
    factor X (n + 2) * (Y * Y) =
      (corner X Y Z (n + 2) * corner X Y Z (n + 1)) * factor X n := by
  have hr1 : factor X (n + 1) * Y = corner X Y Z (n + 1) * factor X n :=
    factor_next_mul hXY hZX n
  have hr2 : factor X (n + 2) * Y =
      corner X Y Z (n + 2) * factor X (n + 1) := by
    simpa only [corner, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      factor_next_mul hXY hZX (n + 1)
  rw [← mul_assoc, hr2, mul_assoc, hr1, ← mul_assoc]

/-- Left normalization of the compact polynomial corner, for arbitrary two natural parameters. -/
theorem left_factorization
    (hXY : X * Y - Y * X = Z) (hZY : Z * Y - Y * Z = -X) (a b : ℕ) :
    factor X a * factor Y (a + b) =
      factor Y b * normalLeft X Y Z a (b : ℂ) := by
  induction a using Nat.twoStepInduction generalizing b with
  | zero => simp [factor, normalLeft]
  | one =>
      simpa only [factor, normalLeft, Nat.add_comm] using left_shift hXY hZY b
  | more a ih _ =>
      have hi := ih (b + 2)
      have hL := left_square hXY hZY b
      have hY := factor_right_add_two Y b
      simp only [Nat.cast_add, Nat.cast_ofNat] at hi
      rw [show a + 2 + b = a + (b + 2) by omega]
      rw [factor]
      simp only [add_mul, mul_assoc, smul_mul_assoc, hi]
      rw [normalLeft]
      linear_combination (norm := (simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc]; noncomm_ring))
        hL * normalLeft X Y Z a ((b : ℂ) + 2) +
        ((a + 1 : ℂ) ^ 2) • hY * normalLeft X Y Z a ((b : ℂ) + 2)

/-- Right normalization of the other compact polynomial corner. -/
theorem right_factorization
    (hXY : X * Y - Y * X = Z) (hZX : Z * X - X * Z = Y) (a b : ℕ) :
    factor X (a + b) * factor Y a =
      normalRight X Y Z a (b : ℂ) * factor X b := by
  induction a using Nat.twoStepInduction generalizing b with
  | zero => simp [factor, normalRight]
  | one =>
      simpa only [factor, normalRight, corner, Nat.add_comm] using factor_next_mul hXY hZX b
  | more a ih _ =>
      have hi := ih (b + 2)
      have hR := right_square hXY hZX b
      have hX := factor_add_two X b
      simp only [Nat.cast_add, Nat.cast_ofNat] at hi
      rw [show a + 2 + b = a + (b + 2) by omega]
      rw [factor_right_add_two Y a, ← mul_assoc, hi]
      rw [normalRight]
      linear_combination (norm := (simp only [Algebra.algebraMap_eq_smul_one]; noncomm_ring))
        normalRight X Y Z a ((b : ℂ) + 2) * hR +
        ((a + 1 : ℂ) ^ 2) • (normalRight X Y Z a ((b : ℂ) + 2) * hX)

/-- Equality of the recursive corner expressions suffices; no factor is cancelled. -/
theorem braid_of_normal_eq
    (hXY : X * Y - Y * X = Z) (hZX : Z * X - X * Z = Y)
    (hZY : Z * Y - Y * Z = -X) (a b : ℕ)
    (hN : normalLeft X Y Z a (b : ℂ) = normalRight X Y Z a (b : ℂ)) :
    factor X a * factor Y (a + b) * factor X b =
      factor Y b * factor X (a + b) * factor Y a := by
  rw [left_factorization hXY hZY a b, hN, mul_assoc,
    ← right_factorization hXY hZX a b, ← mul_assoc]

end Langlands.Archimedean.RealCompactPolynomialFullBraid

namespace Langlands.Archimedean

/-- The full two-parameter compact central-factorial braid. This proposition is
isolated here as an unproved algebraic prerequisite. -/
def RealCompactPolynomialFullBraidStatement : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (X Y Z : A),
    X * Y - Y * X = Z → Z * X - X * Z = Y → Z * Y - Y * Z = -X →
      ∀ a b : ℕ,
        RealCompactPolynomialRelations.factor X a *
            RealCompactPolynomialRelations.factor Y (a + b) *
            RealCompactPolynomialRelations.factor X b =
          RealCompactPolynomialRelations.factor Y b *
            RealCompactPolynomialRelations.factor X (a + b) *
            RealCompactPolynomialRelations.factor Y a

end Langlands.Archimedean
