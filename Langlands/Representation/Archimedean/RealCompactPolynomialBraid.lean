import Langlands.Representation.Archimedean.RealCompactPolynomialRelations
import Mathlib.Algebra.Algebra.Opposite

/-! # The first-parameter compact polynomial braid -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Archimedean.RealCompactPolynomialBraid

open RealCompactPolynomialRelations MulOpposite

variable {A : Type*} [Ring A] [Algebra ℂ A]

private theorem factor_commutes (X : A) (n : ℕ) : factor X n * X = X * factor X n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [factor]
  | one => rfl
  | more n ih _ =>
      simp only [factor, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_assoc, ih]

private theorem unop_factor (X : Aᵐᵒᵖ) (n : ℕ) :
    unop (factor X n) = factor (unop X) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [factor]
  | one => rfl
  | more n ih _ =>
      simp only [factor, unop_add, unop_mul, unop_smul, ih]
      congr 1
      calc
        factor (unop X) n * (unop X * unop X) =
            (factor (unop X) n * unop X) * unop X := (mul_assoc _ _ _).symm
        _ = (unop X * factor (unop X) n) * unop X := by rw [factor_commutes]
        _ = (unop X * unop X) * factor (unop X) n := by
          rw [mul_assoc, factor_commutes, ← mul_assoc]

variable {X Y Z : A}

/-- The matching first-order relation with the generator on the left. -/
theorem mul_factor_next
    (hXY : X * Y - Y * X = Z)
    (hZX : Z * X - X * Z = Y) (n : ℕ) :
    Y * factor X (n + 1) = factor X n * (X * Y - (n + 1 : ℂ) • Z) := by
  have hXY' : op X * op Y - op Y * op X = -op Z := by
    apply unop_injective
    simp only [unop_sub, unop_mul, unop_op, unop_neg]
    linear_combination (norm := noncomm_ring) -hXY
  have hZX' : (-op Z) * op X - op X * (-op Z) = op Y := by
    apply unop_injective
    simp only [unop_sub, unop_mul, unop_op, unop_neg]
    linear_combination (norm := noncomm_ring) hZX
  have h := congrArg unop (factor_next_mul hXY' hZX' n)
  simpa only [unop_mul, unop_factor, unop_op, unop_add, unop_smul,
    unop_neg, smul_neg, sub_eq_add_neg] using h

/-- The polynomial braid holds for first parameter one and every natural second parameter. -/
theorem braid_one_nat
    (hXY : X * Y - Y * X = Z)
    (hZX : Z * X - X * Z = Y)
    (hZY : Z * Y - Y * Z = -X) (n : ℕ) :
    X * factor Y (n + 1) * factor X n =
      factor Y n * factor X (n + 1) * Y := by
  have hYX : Y * X - X * Y = -Z := by
    linear_combination (norm := noncomm_ring) -hXY
  have hZY' : (-Z) * Y - Y * (-Z) = X := by
    linear_combination (norm := noncomm_ring) -hZY
  have hleft := mul_factor_next hYX hZY' n
  simp only [smul_neg, sub_neg_eq_add] at hleft
  rw [hleft, mul_assoc, ← factor_next_mul hXY hZX, ← mul_assoc]

/-- The polynomial braid with first parameter two and arbitrary natural second parameter. -/
theorem braid_two_nat
    (hXY : X * Y - Y * X = Z)
    (hZX : Z * X - X * Z = Y)
    (hZY : Z * Y - Y * Z = -X) (n : ℕ) :
    factor X 2 * factor Y (n + 2) * factor X n =
      factor Y n * factor X (n + 2) * factor Y 2 := by
  let R (t : ℂ) : A := Y * X + t • Z
  have hYX : Y * X - X * Y = -Z := by
    linear_combination (norm := noncomm_ring) -hXY
  have hZY' : (-Z) * Y - Y * (-Z) = X := by
    linear_combination (norm := noncomm_ring) -hZY
  have hl1 : X * factor Y (n + 1) = factor Y n * R (n + 1) := by
    simpa only [R, smul_neg, sub_neg_eq_add] using mul_factor_next hYX hZY' n
  have hl2 : X * factor Y (n + 2) = factor Y (n + 1) * R (n + 2) := by
    simpa only [R, smul_neg, sub_neg_eq_add, Nat.cast_add, Nat.cast_one,
      add_assoc, one_add_one_eq_two] using mul_factor_next hYX hZY' (n + 1)
  have hr1 : factor X (n + 1) * Y = R (n + 1) * factor X n :=
    factor_next_mul hXY hZX n
  have hr2 : factor X (n + 2) * Y = R (n + 2) * factor X (n + 1) := by
    simpa only [R, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      factor_next_mul hXY hZX (n + 1)
  have hLS : (X * X) * factor Y (n + 2) =
      factor Y n * (R (n + 1) * R (n + 2)) := by
    rw [mul_assoc, hl2, ← mul_assoc, hl1, mul_assoc]
  have hRS : factor X (n + 2) * (Y * Y) =
      (R (n + 2) * R (n + 1)) * factor X n := by
    rw [← mul_assoc, hr2, mul_assoc, hr1, ← mul_assoc]
  have hY : factor Y (n + 2) =
      factor Y n * (Y * Y + algebraMap ℂ A ((n + 1 : ℂ) ^ 2)) := by
    rw [factor_add_two]
    simp only [add_mul, mul_add, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    rw [mul_assoc, ← factor_commutes, ← mul_assoc, ← factor_commutes]
    simp only [mul_assoc]
  have hcomm : (Y * X) * Z - Z * (Y * X) = X * X - Y * Y := by
    linear_combination (norm := noncomm_ring) -Y * hZX - hZY * X
  have hmid : R (n + 1) * R (n + 2) + Y * Y =
      R (n + 2) * R (n + 1) + X * X := by
    dsimp [R]
    linear_combination (norm := (noncomm_ring; module)) hcomm
  have hX := factor_add_two X n
  have hx2 : factor X 2 = X * X + 1 := by norm_num [factor]
  have hy2 : factor Y 2 = Y * Y + 1 := by norm_num [factor]
  rw [hx2, hy2]
  calc
    (X * X + 1) * factor Y (n + 2) * factor X n =
        factor Y n * (R (n + 1) * R (n + 2) + Y * Y +
          algebraMap ℂ A ((n + 1 : ℂ) ^ 2)) * factor X n := by
      linear_combination (norm := noncomm_ring) hLS * factor X n + hY * factor X n
    _ = factor Y n * (R (n + 2) * R (n + 1) + X * X +
          algebraMap ℂ A ((n + 1 : ℂ) ^ 2)) * factor X n := by rw [hmid]
    _ = factor Y n * factor X (n + 2) * (Y * Y + 1) := by
      linear_combination (norm := noncomm_ring) -factor Y n * hRS - factor Y n * hX

end Langlands.Archimedean.RealCompactPolynomialBraid

namespace Langlands.Archimedean

/-- The compact polynomial braid for first parameter one or two and arbitrary
natural second parameter, under the actual orthogonal commutator relations. -/
def RealCompactPolynomialBraidStatement : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (X Y Z : A),
    X * Y - Y * X = Z → Z * X - X * Z = Y → Z * Y - Y * Z = -X →
      ∀ n : ℕ,
        X * RealCompactPolynomialRelations.factor Y (n + 1) *
            RealCompactPolynomialRelations.factor X n =
          RealCompactPolynomialRelations.factor Y n *
            RealCompactPolynomialRelations.factor X (n + 1) * Y ∧
        RealCompactPolynomialRelations.factor X 2 *
            RealCompactPolynomialRelations.factor Y (n + 2) *
            RealCompactPolynomialRelations.factor X n =
          RealCompactPolynomialRelations.factor Y n *
            RealCompactPolynomialRelations.factor X (n + 2) *
            RealCompactPolynomialRelations.factor Y 2

theorem realCompactPolynomialBraid : RealCompactPolynomialBraidStatement := by
  intro A _ _ X Y Z hXY hZX hZY n
  exact ⟨RealCompactPolynomialBraid.braid_one_nat hXY hZX hZY n,
    RealCompactPolynomialBraid.braid_two_nat hXY hZX hZY n⟩

end Langlands.Archimedean
