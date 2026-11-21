import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-!
# Quaternionic matrices for the real rank-four exponent bound

The two compact triples are half left and half right quaternion multiplication.
Their products, scaled by two, are the nine trace-free symmetric matrices.
-/

set_option autoImplicit false

namespace Langlands.Archimedean.RealRankFourMatrices

open Matrix
open scoped BigOperators

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Rows and columns are indexed by `(1, i, j, k)`, and the left triple is
ordered `(j, k, i)`. -/
private def leftQ : Fin 3 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![!![0, 0, -1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, -1, 0, 0],
    !![0, 0, 0, -1; 0, 0, -1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
    !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]]

/-- The order `(k, j, i)` compensates for the reverse multiplication law
of right quaternion multiplication. -/
private def rightQ : Fin 3 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![!![0, 0, 0, -1; 0, 0, 1, 0; 0, -1, 0, 0; 1, 0, 0, 0],
    !![0, 0, -1, 0; 0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 0],
    !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]]

/-- The quaternionic basis with the identity in position `(0, 0)`. -/
def basisQ (b : Fin 4 × Fin 4) : Matrix (Fin 4) (Fin 4) ℚ :=
  (1 / 2 : ℚ) • (Fin.cases 1 leftQ b.1 * Fin.cases 1 rightQ b.2)

/-- The diagonal of the trace-dual matrix in the quaternionic basis. -/
def signQ (b : Fin 4 × Fin 4) : ℚ :=
  (if b.1 = 0 then 1 else -1) * (if b.2 = 0 then 1 else -1)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
/-- The canonical trace tensor has coefficient one precisely when two
entry indices are exchanged. This checks the actual tensor of coefficients. -/
theorem traceTensorQ (p q : Fin 4 × Fin 4) :
    ∑ b : Fin 4 × Fin 4, signQ b * basisQ b p.1 p.2 * basisQ b q.1 q.2 =
      if q = p.swap then 1 else 0 := by
  revert p q
  decide +kernel

/-- The two skew triples and a column of symmetric matrices admit a common
normalization. -/
abbrev KQ (i : Fin 3) := basisQ (i.succ, 0)
abbrev RQ (j : Fin 3) := basisQ (0, j.succ)
abbrev PQ (i j : Fin 3) := basisQ (i.succ, j.succ)

def commQ (X Y : Matrix (Fin 4) (Fin 4) ℚ) := X * Y - Y * X

theorem left_commQ :
    commQ (KQ 0) (KQ 1) = KQ 2 ∧ commQ (KQ 1) (KQ 2) = KQ 0 ∧
      commQ (KQ 2) (KQ 0) = KQ 1 := by decide +kernel

theorem left_column_commQ (j : Fin 3) :
    commQ (KQ 0) (PQ 0 j) = 0 ∧ commQ (KQ 0) (PQ 1 j) = PQ 2 j ∧
    commQ (KQ 0) (PQ 2 j) = -PQ 1 j ∧ commQ (KQ 1) (PQ 0 j) = -PQ 2 j ∧
    commQ (KQ 1) (PQ 1 j) = 0 ∧ commQ (KQ 1) (PQ 2 j) = PQ 0 j ∧
    commQ (KQ 2) (PQ 0 j) = PQ 1 j ∧ commQ (KQ 2) (PQ 1 j) = -PQ 0 j := by
  revert j
  decide +kernel

theorem column_commQ (j : Fin 3) : commQ (PQ 0 j) (PQ 1 j) = -KQ 2 := by
  revert j
  decide +kernel

@[simp] theorem KQ_transpose (i : Fin 3) : (KQ i)ᵀ = -KQ i := by
  revert i
  decide +kernel

@[simp] theorem RQ_transpose (j : Fin 3) : (RQ j)ᵀ = -RQ j := by
  revert j
  decide +kernel

theorem basisQ_zero : basisQ (0, 0) = (1 / 2 : ℚ) • 1 := by
  change (1 / 2 : ℚ) • ((1 : Matrix (Fin 4) (Fin 4) ℚ) * 1) = _
  rw [mul_one]

private theorem KQ_eq (i : Fin 3) : KQ i = (1 / 2 : ℚ) • leftQ i := by
  change (1 / 2 : ℚ) • (leftQ i * 1) = _
  rw [mul_one]

private theorem RQ_eq (j : Fin 3) : RQ j = (1 / 2 : ℚ) • rightQ j := by
  change (1 / 2 : ℚ) • (1 * rightQ j) = _
  rw [one_mul]

section ScalarExtension

noncomputable section

abbrev MatR := Matrix (Fin 4) (Fin 4) ℝ
abbrev MatC := Matrix (Fin 4) (Fin 4) ℂ

def basisR (b : Fin 4 × Fin 4) : MatR := (Rat.castHom ℝ).mapMatrix (basisQ b)
def basisC (b : Fin 4 × Fin 4) : MatC := (Rat.castHom ℂ).mapMatrix (basisQ b)

abbrev K (i : Fin 3) := basisC (i.succ, 0)
abbrev R (j : Fin 3) := basisC (0, j.succ)
abbrev P (i j : Fin 3) := basisC (i.succ, j.succ)

@[simp] theorem basisC_apply (b : Fin 4 × Fin 4) (i j : Fin 4) :
    basisC b i j = (basisQ b i j : ℂ) := rfl

private theorem K_apply (i : Fin 3) (p q : Fin 4) :
    K i p q = ((1 / 2 : ℚ) * leftQ i p q : ℚ) := by
  change (KQ i p q : ℂ) = _
  rw [KQ_eq, Matrix.smul_apply, smul_eq_mul]

private theorem R_apply (i : Fin 3) (p q : Fin 4) :
    R i p q = ((1 / 2 : ℚ) * rightQ i p q : ℚ) := by
  change (RQ i p q : ℂ) = _
  rw [RQ_eq, Matrix.smul_apply, smul_eq_mul]

/-- With `i` the imaginary unit, the columns span the `i/2`-eigenspace
of `K 2`. The polynomial construction also uses this matrix over its
coefficient polynomial ring. -/
def highestPlane {A : Type*} [Ring A] (i : A) : Matrix (Fin 4) (Fin 2) A :=
  !![1, 0; -i, 0; 0, 1; 0, -i]

open Complex in
theorem K_mul_highestPlane :
    K 0 * highestPlane I = I • (K 1 * highestPlane I) ∧
    K 2 * highestPlane I = (I / 2) • highestPlane I := by
  constructor <;> ext j k <;>
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, K_apply] <;>
    fin_cases j <;> fin_cases k <;>
    norm_num [leftQ, highestPlane, Fin.sum_univ_four, ← pow_two, I_sq] <;>
    ring_nf <;> norm_num [I_sq]

open Complex in
def rightPlaneAction : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, I / 2; I / 2, 0], !![0, -1 / 2; 1 / 2, 0], !![I / 2, 0; 0, -I / 2]]

open Complex in
theorem R_mul_highestPlane (j : Fin 3) :
    R j * highestPlane I = highestPlane I * rightPlaneAction j := by
  ext i k
  simp only [Matrix.mul_apply, R_apply]
  fin_cases j <;> fin_cases i <;> fin_cases k <;>
    norm_num [rightQ, highestPlane, rightPlaneAction, Fin.sum_univ_four, Fin.sum_univ_two,
      ← pow_two, I_sq] <;> ring_nf <;> norm_num [I_sq]

theorem ofReal_basisR (b : Fin 4 × Fin 4) :
    Complex.ofRealHom.mapMatrix (basisR b) = basisC b := by
  ext p q
  exact Complex.ofReal_ratCast _

@[simp] theorem basisR_apply (b : Fin 4 × Fin 4) (i j : Fin 4) :
    basisR b i j = (basisQ b i j : ℝ) := rfl

theorem basisR_K_transpose (i : Fin 3) :
    (basisR (i.succ, 0))ᵀ = -basisR (i.succ, 0) := by
  ext p q
  change (KQ i q p : ℝ) = -(KQ i p q : ℝ)
  rw [← Rat.cast_neg]
  exact congrArg (fun X : Matrix (Fin 4) (Fin 4) ℚ => (X p q : ℝ)) (KQ_transpose i)

theorem basisR_R_transpose (j : Fin 3) :
    (basisR (0, j.succ))ᵀ = -basisR (0, j.succ) := by
  ext p q
  change (RQ j q p : ℝ) = -(RQ j p q : ℝ)
  rw [← Rat.cast_neg]
  exact congrArg (fun X : Matrix (Fin 4) (Fin 4) ℚ => (X p q : ℝ)) (RQ_transpose j)

private theorem lie_of_commQ {X Y Z : Matrix (Fin 4) (Fin 4) ℚ}
    (h : commQ X Y = Z) :
    ⁅(Rat.castHom ℂ).mapMatrix X, (Rat.castHom ℂ).mapMatrix Y⁆ =
      (Rat.castHom ℂ).mapMatrix Z := by
  rw [← h, commQ, map_sub, map_mul, map_mul, LieRing.of_associative_ring_bracket]

theorem left_lie :
    ⁅K 0, K 1⁆ = K 2 ∧ ⁅K 1, K 2⁆ = K 0 ∧ ⁅K 2, K 0⁆ = K 1 :=
  ⟨lie_of_commQ left_commQ.1, lie_of_commQ left_commQ.2.1, lie_of_commQ left_commQ.2.2⟩

theorem left_column_lie (j : Fin 3) :
    ⁅K 0, P 0 j⁆ = 0 ∧ ⁅K 0, P 1 j⁆ = P 2 j ∧ ⁅K 0, P 2 j⁆ = -P 1 j ∧
    ⁅K 1, P 0 j⁆ = -P 2 j ∧ ⁅K 1, P 1 j⁆ = 0 ∧ ⁅K 1, P 2 j⁆ = P 0 j ∧
    ⁅K 2, P 0 j⁆ = P 1 j ∧ ⁅K 2, P 1 j⁆ = -P 0 j := by
  obtain ⟨h00, h01, h02, h10, h11, h12, h20, h21⟩ := left_column_commQ j
  refine ⟨?_, lie_of_commQ h01, ?_, ?_, ?_, lie_of_commQ h12, lie_of_commQ h20, ?_⟩
  · simpa only [basisC, map_zero] using lie_of_commQ h00
  · simpa only [basisC, map_neg] using lie_of_commQ h02
  · simpa only [basisC, map_neg] using lie_of_commQ h10
  · simpa only [basisC, map_zero] using lie_of_commQ h11
  · simpa only [basisC, map_neg] using lie_of_commQ h21

open Complex in
def raising : MatC := K 0 - I • K 1

open Complex in
def lowering : MatC := -K 0 - I • K 1

open Complex in
def cartan : MatC := (-2 : ℂ) • (I • K 2)

open Complex in
def upperColumn (j : Fin 3) : MatC := P 0 j - I • P 1 j

open Complex in
def lowerColumn (j : Fin 3) : MatC := P 0 j + I • P 1 j

open Complex in
theorem raising_lie_lowering : ⁅raising, lowering⁆ = cartan := by
  have h := left_lie.1
  have h' : ⁅K 1, K 0⁆ = -K 2 := by rw [← lie_skew, h]
  simp only [raising, lowering, cartan, sub_lie, lie_sub, smul_lie, lie_smul,
    lie_neg, lie_self, h, h', smul_zero]
  module

open Complex in
theorem cartan_lie_lowering : ⁅cartan, lowering⁆ = (-2 : ℂ) • lowering := by
  have h := left_lie.2.2
  have h' : ⁅K 2, K 1⁆ = -K 0 := by rw [← lie_skew, left_lie.2.1]
  simp only [cartan, lowering, lie_sub, smul_lie, lie_smul, lie_neg, h, h',
    smul_sub, smul_neg, smul_smul]
  match_scalars <;> ring_nf
  norm_num [pow_two, I_mul_I]

open Complex in
theorem raising_lie_upperColumn (j : Fin 3) : ⁅raising, upperColumn j⁆ = 0 := by
  obtain ⟨h00, h01, _, h10, h11, _, _, _⟩ := left_column_lie j
  simp only [raising, upperColumn, sub_lie, lie_sub, smul_lie, lie_smul,
    h00, h01, h10, h11, smul_zero, smul_neg]
  module

open Complex in
theorem cartan_lie_upperColumn (j : Fin 3) :
    ⁅cartan, upperColumn j⁆ = (2 : ℂ) • upperColumn j := by
  obtain ⟨_, _, _, _, _, _, h20, h21⟩ := left_column_lie j
  simp only [cartan, upperColumn, lie_sub, smul_lie, lie_smul, h20, h21,
    smul_sub, smul_neg, smul_smul]
  match_scalars <;> ring_nf
  norm_num [pow_two, I_mul_I]

open Complex in
theorem raising_lie_middleColumn (j : Fin 3) : ⁅raising, P 2 j⁆ = -I • upperColumn j := by
  obtain ⟨_, _, h02, _, _, h12, _, _⟩ := left_column_lie j
  simp only [raising, upperColumn, sub_lie, smul_lie, h02, h12, smul_sub,
    smul_smul, neg_mul, I_mul_I]
  module

open Complex in
theorem raising_lie_lowerColumn (j : Fin 3) :
    ⁅raising, lowerColumn j⁆ = (2 * I) • P 2 j := by
  obtain ⟨h00, h01, _, h10, h11, _, _, _⟩ := left_column_lie j
  simp only [raising, lowerColumn, sub_lie, lie_add, smul_lie, lie_smul,
    h00, h01, h10, h11, smul_zero, smul_neg]
  module

open Complex in
theorem upperColumn_lie_lowerColumn (j : Fin 3) : ⁅upperColumn j, lowerColumn j⁆ = cartan := by
  have h : ⁅P 0 j, P 1 j⁆ = -K 2 := by
    simpa only [basisC, map_neg] using lie_of_commQ (column_commQ j)
  have h' : ⁅P 1 j, P 0 j⁆ = K 2 := by rw [← lie_skew, h, neg_neg]
  simp only [upperColumn, lowerColumn, cartan, sub_lie, lie_add, smul_lie,
    lie_smul, lie_self, h, h', smul_zero]
  module

/-- Rational coefficient verification after extending scalars. -/
theorem traceTensorC (p q : Fin 4 × Fin 4) :
    ∑ b : Fin 4 × Fin 4, (signQ b : ℂ) * basisC b p.1 p.2 * basisC b q.1 q.2 =
      if q = p.swap then 1 else 0 := by
  have h := congrArg (Rat.castHom ℂ) (traceTensorQ p q)
  simpa only [map_sum, map_mul, apply_ite, map_one, map_zero, basisC_apply, Rat.coe_castHom] using h

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The matrix-unit Casimir expressed as the sum of squared basis actions
with the trace-dual signs. -/
theorem traceTensor_action (A : MatC →ₗ[ℂ] Module.End ℂ V) :
    ∑ b : Fin 4 × Fin 4, (signQ b : ℂ) • (A (basisC b) * A (basisC b)) =
      ∑ p : Fin 4 × Fin 4, A (single p.1 p.2 1) * A (single p.2 p.1 1) := by
  let E (p : Fin 4 × Fin 4) := A (single p.1 p.2 1)
  have expand (X : MatC) :
      A X = ∑ p : Fin 4 × Fin 4, X p.1 p.2 • E p := by
    rw [Fintype.sum_prod_type]
    simp only [E, ← map_smul, smul_single, smul_eq_mul, mul_one, ← map_sum]
    rw [← matrix_eq_sum_single]
  have product (X : MatC) :
      A X * A X = ∑ p : Fin 4 × Fin 4, ∑ q : Fin 4 × Fin 4,
        (X p.1 p.2 * X q.1 q.2) • (E p * E q) := by
    rw [expand X, Finset.sum_mul]
    simp_rw [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
  change _ = ∑ p : Fin 4 × Fin 4, E p * E p.swap
  calc
    _ = ∑ b : Fin 4 × Fin 4, ∑ p : Fin 4 × Fin 4, ∑ q : Fin 4 × Fin 4,
        ((signQ b : ℂ) * basisC b p.1 p.2 * basisC b q.1 q.2) • (E p * E q) := by
          simp only [product, Finset.smul_sum, smul_smul, mul_assoc]
    _ = ∑ p : Fin 4 × Fin 4, ∑ q : Fin 4 × Fin 4,
        (∑ b : Fin 4 × Fin 4, (signQ b : ℂ) * basisC b p.1 p.2 * basisC b q.1 q.2) •
          (E p * E q) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_comm]
          simp only [Finset.sum_smul]
    _ = _ := by
      simp only [traceTensorC, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]

/-- In the trace tensor the symmetric matrices and the center occur with
positive sign, and the two skew triples occur with negative sign. -/
theorem casimir_split (A : MatC →ₗ[ℂ] Module.End ℂ V) :
    (∑ p : Fin 4, ∑ q : Fin 4, A (single p q 1) * A (single q p 1)) =
      (∑ i : Fin 3, ∑ j : Fin 3, A (P i j) ^ 2) -
      (∑ i : Fin 3, A (K i) ^ 2) - (∑ j : Fin 3, A (R j) ^ 2) +
      A (basisC (0, 0)) ^ 2 := by
  rw [← Fintype.sum_prod_type (fun p : Fin 4 × Fin 4 => A (single p.1 p.2 1) *
    A (single p.2 p.1 1)), ← traceTensor_action, Fintype.sum_prod_type,
    Fin.sum_univ_succ]
  simp_rw [Fin.sum_univ_succ (n := 3)]
  have h00 : (signQ (0, 0) : ℂ) = 1 := by norm_num [signQ]
  have h0j (j : Fin 3) : (signQ (0, j.succ) : ℂ) = -1 := by
    norm_num [signQ, Fin.succ_ne_zero]
  have hi0 (i : Fin 3) : (signQ (i.succ, 0) : ℂ) = -1 := by
    norm_num [signQ, Fin.succ_ne_zero]
  have hij (i j : Fin 3) : (signQ (i.succ, j.succ) : ℂ) = 1 := by
    norm_num [signQ, Fin.succ_ne_zero]
  simp only [h00, h0j, hi0, hij, one_smul, neg_smul, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, pow_two]
  abel

end

end ScalarExtension

end Langlands.Archimedean.RealRankFourMatrices
