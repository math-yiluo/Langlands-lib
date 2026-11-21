import Langlands.GroupScheme.Quaternionic.QuaternionicSplitConjugation
import Langlands.GroupScheme.Quaternionic.ScalarQuadratic
import Mathlib.Data.Matrix.Composition

/-! # Scalar Gram coordinates for a split skew-hermitian pairing -/

noncomputable section

universe u v w

open Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000

section SplitCoordinates

variable {R : Type u} {A : Type v} [Field R] [Ring A] [Algebra R A]
  {I : Type w} (e : A ≃ₐ[R] Matrix (Fin 2) (Fin 2) R)

local notation "M₂" => Matrix (Fin 2) (Fin 2) R
local notation "J" => FirstKindInvolution.gramTwo R

/-- The two scalar rows in the chosen chart of every quaternion coordinate. -/
def splitSkewRows (x : I → A) : Matrix (Fin 2) (I × Fin 2) R :=
  Matrix.of fun a ⟨i, b⟩ => e (x i) a b

/-- Recombine two scalar rows into a quaternionic row. -/
def fromSplitSkewRows (X : Matrix (Fin 2) (I × Fin 2) R) : I → A :=
  fun i => e.symm (Matrix.of fun a b => X a (i, b))

@[simp] theorem splitSkewRows_fromSplitSkewRows (X : Matrix (Fin 2) (I × Fin 2) R) :
    splitSkewRows e (fromSplitSkewRows e X) = X := by
  ext a ⟨i, b⟩
  simp [splitSkewRows, fromSplitSkewRows]

/-- The scalar Gram matrix is formed by multiplying each two-by-two block
  on the right by the standard alternating matrix and flattening. -/
def splitSkewScalarGram (H : Matrix I I A) : Matrix (I × Fin 2) (I × Fin 2) R :=
  Matrix.comp I I (Fin 2) (Fin 2) R (H.map fun a => e a * J)

@[simp] theorem splitSkewScalarGram_apply (H : Matrix I I A) (i j : I) (a b : Fin 2) :
    splitSkewScalarGram e H (i, a) (j, b) = (e (H i j) * J) a b := rfl

private theorem gramTwo_transpose : (J : M₂)ᵀ = -J := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [FirstKindInvolution.gramTwo]

variable [Fintype I] [DecidableEq I]

/-- Invertibility survives the scalar Gram construction. -/
theorem splitSkewScalarGram_isUnit {H : Matrix I I A} (hH : IsUnit H) :
    IsUnit (splitSkewScalarGram e H) := by
  let L := Matrix.diagonal (fun _ : I => J)
  have hL : IsUnit L :=
    (Pi.isUnit_iff.mpr (fun _ : I => FirstKindInvolution.isUnit_gramTwo (D := R))).map
      (Matrix.diagonalRingHom I M₂)
  have hprod : splitSkewScalarGram e H = (Matrix.compRingEquiv I (Fin 2) R)
      ((H.map e) * L) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    rw [splitSkewScalarGram_apply, Matrix.compRingEquiv_apply, Matrix.comp_apply]
    change (e (H i j) * J) a b = ((H.map e) * Matrix.diagonal (fun _ : I => J)) i j a b
    rw [Matrix.mul_diagonal, Matrix.map_apply]
  rw [hprod]
  have hmap : IsUnit (H.map e) := hH.map (e.mapMatrix (m := I))
  exact (hmap.mul hL).map (Matrix.compRingEquiv I (Fin 2) R)

variable (τ : FirstKindInvolution R A)
  (hτ : ∀ z : A, e (τ z) * FirstKindInvolution.gramTwo R =
    FirstKindInvolution.gramTwo R * (e z)ᵀ)

include hτ in
/-- The negative adjoint equation makes the scalar Gram matrix symmetric. -/
theorem splitSkewScalarGram_isSymm {H : Matrix I I A} (hH : τ.matrix I H = -H) :
    (splitSkewScalarGram e H).IsSymm := by
  change (splitSkewScalarGram e H)ᵀ = splitSkewScalarGram e H
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [Matrix.transpose_apply, splitSkewScalarGram_apply, splitSkewScalarGram_apply]
  have h : τ (H j i) = -(H i j) := congrArg (fun M : Matrix I I A => M i j) hH
  have ht : (e (H j i) * J)ᵀ = e (H i j) * J := by
    rw [Matrix.transpose_mul, gramTwo_transpose (R := R), Matrix.neg_mul, ← hτ (H j i), h,
      map_neg, Matrix.neg_mul, neg_neg]
  exact congrArg (fun M : M₂ => M a b) ht

private theorem comp_mul_rectangular {I₁ I₂ I₃ : Type*} [Fintype I₂]
    (P : Matrix I₁ I₂ M₂) (Q : Matrix I₂ I₃ M₂) :
    Matrix.comp I₁ I₃ (Fin 2) (Fin 2) R (P * Q) =
      Matrix.comp I₁ I₂ (Fin 2) (Fin 2) R P * Matrix.comp I₂ I₃ (Fin 2) (Fin 2) R Q := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Matrix.comp_apply, Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]

omit [DecidableEq I] in
include hτ in
/-- Multiplying the skew value by the alternating matrix gives the two scalar
  rows paired by the scalar Gram matrix. -/
theorem matrixSesqBilin_splitSkewScalarGram (H : Matrix I I A) (x y : I → A) :
    e (τ.matrixSesqBilin H x y) * J =
      splitSkewRows e x * splitSkewScalarGram e H * (splitSkewRows e y)ᵀ := by
  let P : Matrix Unit I M₂ := Matrix.of fun _ i => e (x i)
  let Q : Matrix I I M₂ := H.map fun a => e a * J
  let T : Matrix I Unit M₂ := Matrix.of fun i _ => (e (y i))ᵀ
  have hval : e (τ.matrixSesqBilin H x y) * J =
      ∑ i, ∑ j, e (x i) * (e (H i j) * J) * (e (y j))ᵀ := by
    rw [FirstKindInvolution.matrixSesqBilin_apply]
    simp only [map_sum, map_mul, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_assoc (e (x i) * e (H i j)), hτ (y j)]
    all_goals simp only [mul_assoc]
  have hblocks : (P * Q * T) () () = e (τ.matrixSesqBilin H x y) * J := by
    rw [hval, Matrix.mul_apply, Finset.sum_comm]
    simp only [Matrix.mul_apply, Matrix.sum_mul, P, Q, T, Matrix.of_apply, Matrix.map_apply]
  have hflat : Matrix.comp Unit Unit (Fin 2) (Fin 2) R (P * Q * T) =
      Matrix.comp Unit I (Fin 2) (Fin 2) R P * splitSkewScalarGram e H *
        Matrix.comp I Unit (Fin 2) (Fin 2) R T := by
    rw [comp_mul_rectangular, comp_mul_rectangular]
    rfl
  ext a b
  rw [← hblocks]
  have h := congrArg (fun M : Matrix (Unit × Fin 2) (Unit × Fin 2) R => M ((), a) ((), b)) hflat
  calc
    _ = (Matrix.comp Unit I (Fin 2) (Fin 2) R P * splitSkewScalarGram e H *
        Matrix.comp I Unit (Fin 2) (Fin 2) R T) ((), a) ((), b) := h
    _ = _ := by
      simp only [Matrix.mul_apply, Matrix.comp_apply, P, T, splitSkewRows,
        Matrix.of_apply, Matrix.transpose_apply]

end SplitCoordinates

open FirstKindInvolution

/-- The split scalar Gram construction preserves invertibility and computes
  quaternionic skew values in the two scalar rows. -/
def QuaternionicSplitScalarGramStatement : Prop :=
  ∀ (F D R : Type u) [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
    [Algebra.IsCentral F D] [FiniteDimensional F D] [Field R] [Algebra F R]
    (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
    (hsym : Module.finrank F σ.symmetricSubspace = 3)
    (e : R ⊗[F] D ≃ₐ[R] Matrix (Fin 2) (Fin 2) R)
    (I : Type w) [Fintype I] [DecidableEq I] (H : Matrix I I (R ⊗[F] D)),
    let τ := (σ.quaternionConjugation hdim hsym).baseChange R
    τ.matrix I H = -H → IsUnit H →
    (splitSkewScalarGram e H).IsSymm ∧ IsUnit (splitSkewScalarGram e H) ∧
      ∀ x y : I → R ⊗[F] D,
        e (τ.matrixSesqBilin H x y) * gramTwo R =
          splitSkewRows e x * splitSkewScalarGram e H * (splitSkewRows e y)ᵀ

theorem quaternionicSplitScalarGram : QuaternionicSplitScalarGramStatement.{u, w} := by
  intro F D R _ _ _ _ _ _ _ _ σ hdim hsym e I _ _ H τ hH hu
  have hτ := σ.splitQuaternionConjugation_mul_gramTwo hdim hsym e
  exact ⟨splitSkewScalarGram_isSymm e τ hτ hH, splitSkewScalarGram_isUnit e hu,
    matrixSesqBilin_splitSkewScalarGram e τ hτ H⟩

end Langlands.GroupScheme.Quaternionic
