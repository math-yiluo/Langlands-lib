import Langlands.Group.GL.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! # Three-block algebra for the dominant rectangular matrix -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

universe uF uA uC uB

namespace BlockAlgebra

variable {K : Type uF} [CommRing K]
variable {A : Type uA} {C : Type uC} {B : Type uB}
variable [Fintype A] [Fintype C] [Fintype B]
variable [DecidableEq A] [DecidableEq C] [DecidableEq B]

/-- A three-by-three block matrix, with coordinates grouped as `A ⊕ (C ⊕ B)`. -/
def three (aa : Matrix A A K) (ac : Matrix A C K) (ab : Matrix A B K)
    (ca : Matrix C A K) (cc : Matrix C C K) (cb : Matrix C B K)
    (ba : Matrix B A K) (bc : Matrix B C K) (bb : Matrix B B K) :
    Matrix (A ⊕ (C ⊕ B)) (A ⊕ (C ⊕ B)) K :=
  Matrix.fromBlocks aa (Matrix.fromCols ac ab) (Matrix.fromRows ca ba)
    (Matrix.fromBlocks cc cb bc bb)

omit [Fintype A] [Fintype C] [Fintype B] in
@[simp] theorem three_one :
    three (1 : Matrix A A K) (0 : Matrix A C K) (0 : Matrix A B K)
      0 1 0 0 0 1 = 1 := by
  ext i l
  rcases i with i | (i | i) <;> rcases l with l | (l | l) <;>
    simp [three, Matrix.one_apply]

omit [DecidableEq A] [DecidableEq C] [DecidableEq B] in
/-- Ordinary three-block multiplication. -/
theorem three_mul
    (aa aa' : Matrix A A K) (ac ac' : Matrix A C K) (ab ab' : Matrix A B K)
    (ca ca' : Matrix C A K) (cc cc' : Matrix C C K) (cb cb' : Matrix C B K)
    (ba ba' : Matrix B A K) (bc bc' : Matrix B C K) (bb bb' : Matrix B B K) :
    three aa ac ab ca cc cb ba bc bb * three aa' ac' ab' ca' cc' cb' ba' bc' bb' =
      three (aa*aa'+ac*ca'+ab*ba') (aa*ac'+ac*cc'+ab*bc') (aa*ab'+ac*cb'+ab*bb')
        (ca*aa'+cc*ca'+cb*ba') (ca*ac'+cc*cc'+cb*bc') (ca*ab'+cc*cb'+cb*bb')
        (ba*aa'+bc*ca'+bb*ba') (ba*ac'+bc*cc'+bb*bc') (ba*ab'+bc*cb'+bb*bb') := by
  ext i l
  rcases i with i | (i | i) <;> rcases l with l | (l | l) <;>
    simp [three, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

/-- The actual unit `[1,X,0; 0,1,Y; 0,0,1]` when `X*Y=0`. -/
def upper (X : Matrix A C K) (Y : Matrix C B K) (hXY : X * Y = 0) :
    Matrix.GeneralLinearGroup (A ⊕ (C ⊕ B)) K where
  val := three 1 X 0 0 1 Y 0 0 1
  inv := three 1 (-X) 0 0 1 (-Y) 0 0 1
  val_inv := by simp [three_mul, hXY]
  inv_val := by simp [three_mul, hXY]

@[simp] theorem upper_val (X : Matrix A C K) (Y : Matrix C B K) (hXY : X*Y=0) :
    (upper X Y hXY).val = three 1 X 0 0 1 Y 0 0 1 := rfl

@[simp] theorem upper_inv_val (X : Matrix A C K) (Y : Matrix C B K) (hXY : X*Y=0) :
    ((upper X Y hXY)⁻¹).val = three 1 (-X) 0 0 1 (-Y) 0 0 1 := rfl

/-- A lower matrix whose middle block is the identity. -/
def lower (LA : Matrix.GeneralLinearGroup A K) (LB : Matrix.GeneralLinearGroup B K)
    (Z : Matrix B A K) : Matrix.GeneralLinearGroup (A ⊕ (C ⊕ B)) K where
  val := three LA.val 0 0 0 1 0 Z 0 LB.val
  inv := three (LA⁻¹).val 0 0 0 1 0 (-((LB⁻¹).val * Z * (LA⁻¹).val)) 0 (LB⁻¹).val
  val_inv := by
    simp only [three_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hz : Z * (LA⁻¹).val + LB.val * -((LB⁻¹).val * Z * (LA⁻¹).val) = 0 := by
      simp [← Matrix.mul_assoc, -Units.val_mul]
    rw [hz, three_one]
  inv_val := by
    simp only [three_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hz : -((LB⁻¹).val * Z * (LA⁻¹).val) * LA.val + (LB⁻¹).val * Z = 0 := by
      simp [Matrix.mul_assoc, -Units.val_mul]
    rw [hz, three_one]

@[simp] theorem lower_val (LA : Matrix.GeneralLinearGroup A K)
    (LB : Matrix.GeneralLinearGroup B K) (Z : Matrix B A K) :
    (lower (C := C) LA LB Z).val = three LA.val 0 0 0 1 0 Z 0 LB.val := rfl

/-- The internally computed residual unit, rather than an extra supplied covariance premise. -/
def residual (LA : Matrix.GeneralLinearGroup A K) (LB : Matrix.GeneralLinearGroup B K)
    (Z : Matrix B A K) (X : Matrix A C K) (Y : Matrix C B K) (hXY : X*Y=0) :
    Matrix.GeneralLinearGroup (A ⊕ (C ⊕ B)) K :=
  upper X Y hXY * lower LA LB Z *
    (upper ((LA⁻¹).val * X) (Y * LB.val) (by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc X, hXY, Matrix.zero_mul, Matrix.mul_zero]))⁻¹

/-- Its exact three-block formula. -/
theorem residual_val (LA : Matrix.GeneralLinearGroup A K) (LB : Matrix.GeneralLinearGroup B K)
    (Z : Matrix B A K) (X : Matrix A C K) (Y : Matrix C B K) (hXY : X*Y=0) :
    (residual LA LB Z X Y hXY).val =
      three LA.val 0 0 (Y*Z) (1-Y*Z*((LA⁻¹).val*X)) 0
        Z (-Z*((LA⁻¹).val*X)) LB.val := by
  simp only [residual, Units.val_mul, upper_val, upper_inv_val, lower_val, three_mul,
    Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
  have ha : LA.val * -((LA⁻¹).val * X) + X = 0 := by
    simp [← Matrix.mul_assoc, -Units.val_mul]
  have hab : X * -(Y * LB.val) = 0 := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, hXY, Matrix.zero_mul, neg_zero]
  rw [ha, hab]
  congr 1 <;> simp [sub_eq_add_neg, Matrix.mul_assoc, add_comm]

/-- The exact algebraic factorization underlying lower covariance. -/
theorem factorization (LA : Matrix.GeneralLinearGroup A K) (LB : Matrix.GeneralLinearGroup B K)
    (Z : Matrix B A K) (X : Matrix A C K) (Y : Matrix C B K) (hXY : X*Y=0) :
    upper X Y hXY * lower LA LB Z =
      residual LA LB Z X Y hXY *
        upper ((LA⁻¹).val * X) (Y * LB.val) (by
          rw [Matrix.mul_assoc, ← Matrix.mul_assoc X, hXY, Matrix.zero_mul, Matrix.mul_zero]) := by
  simp only [residual, mul_assoc, inv_mul_cancel, mul_one]

end BlockAlgebra

variable {K : Type uF} [CommRing K]

/-- Middle coordinates, including the separating singleton. -/
abbrev Middle (j k : ℕ) := Fin k ⊕ (Fin 1 ⊕ Fin j)

/-- Pad `x` with zero in the last `1+j` middle columns. -/
def padX {a : ℕ} (j : ℕ) {k : ℕ} (x : Matrix (Fin a) (Fin k) K) :
    Matrix (Fin a) (Middle j k) K := Matrix.fromCols x 0

/-- Pad `y` with zero in the first `k+1` middle rows. -/
def padY {b : ℕ} {j : ℕ} (k : ℕ) (y : Matrix (Fin j) (Fin b) K) :
    Matrix (Middle j k) (Fin b) K := Matrix.fromRows 0 (Matrix.fromRows 0 y)

@[simp] theorem padX_mul_padY {a b j k : ℕ}
    (x : Matrix (Fin a) (Fin k) K) (y : Matrix (Fin j) (Fin b) K) :
    padX j x * padY k y = 0 := by
  simp [padX, padY, Matrix.fromCols_mul_fromRows]

@[simp] theorem mul_padX {a j k : ℕ} (M : Matrix (Fin a) (Fin a) K)
    (x : Matrix (Fin a) (Fin k) K) : M * padX j x = padX j (M*x) := by
  simp [padX]

@[simp] theorem padY_mul {b j k : ℕ} (y : Matrix (Fin j) (Fin b) K)
    (M : Matrix (Fin b) (Fin b) K) : padY k y * M = padY k (y*M) := by
  simp [padY, Matrix.fromRows_mul]

end Langlands.RankinSelberg.TwoBlockDominantRectangular
