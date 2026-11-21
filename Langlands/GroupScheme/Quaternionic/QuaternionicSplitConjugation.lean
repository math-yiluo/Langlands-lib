import Langlands.GroupScheme.Quaternionic.QuaternionConjugation
import Langlands.GroupScheme.Quaternionic.StandardGenerationTwo
import Langlands.Algebra.ReducedNormFiniteChart
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # Quaternion conjugation in a two-by-two splitting chart -/

noncomputable section

universe u

open Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open Langlands.CentralSimple

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

variable {F D R : Type u} [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
  [Algebra.IsCentral F D] [FiniteDimensional F D] [Field R] [Algebra F R]
  (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
  (hsym : Module.finrank F σ.symmetricSubspace = 3)

local notation "A" => R ⊗[F] D
local notation "M₂" => Matrix (Fin 2) (Fin 2) R
local notation "barR" => FirstKindInvolution.baseChange (σ.quaternionConjugation hdim hsym) R

/-- The actual quaternion conjugation becomes the adjugate in every
  two-by-two splitting chart. -/
theorem splitQuaternionConjugation_eq_adjugate (e : A ≃ₐ[R] M₂) (a : A) :
    e (barR a) = (e a).adjugate := by
  let U := e a
  let V := e (barR a)
  let j := algebraMap R M₂
  have hnorm (x : A) : e x * e (barR x) = j (e x).det := by
    rw [← _root_.map_mul, σ.quaternionConjugation_norm_baseChange hdim hsym,
      e.commutes, reducedNorm_eq_chart_det_fintype F D e]
  have ha : U * V = j U.det := hnorm a
  have hb : (U + 1) * (V + 1) = j (U + 1).det := by
    simpa only [_root_.map_add, _root_.map_one, (barR).map_add, (barR).map_one] using hnorm (a + 1)
  have hdet : (U + 1).det = U.det + (U 0 0 + U 1 1) + 1 := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two]
    simp only [Matrix.add_apply, Matrix.one_apply, ite_true, show (0 : Fin 2) ≠ 1 by decide,
      show (1 : Fin 2) ≠ 0 by decide, ite_false, add_zero]
    ring
  have hUV : U + V = j (U 0 0 + U 1 1) := by
    have h : U + V + (j U.det + 1) = j (U 0 0 + U 1 1) + (j U.det + 1) := by
      calc
        _ = (U + 1) * (V + 1) := by
          rw [add_mul, mul_add, mul_add, ha, mul_one, one_mul, one_mul]
          abel
        _ = _ := by rw [hb, hdet, _root_.map_add, _root_.map_add, _root_.map_one]; abel
    exact add_right_cancel h
  have hV : V = j (U 0 0 + U 1 1) - U := by rw [← hUV]; abel
  change V = U.adjugate
  rw [hV, Matrix.adjugate_fin_two]
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [j, Matrix.algebraMap_matrix_apply, Matrix.sub_apply]

/-- Quaternion conjugation, followed by right multiplication by the standard
  alternating matrix, is transpose followed by left multiplication. -/
theorem splitQuaternionConjugation_mul_gramTwo (e : A ≃ₐ[R] M₂) (a : A) :
    e (barR a) * gramTwo R = gramTwo R * (e a)ᵀ := by
  rw [σ.splitQuaternionConjugation_eq_adjugate hdim hsym e a, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramTwo, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

/-- The standard quaternion conjugation is the matrix adjugate after splitting. -/
def QuaternionicSplitConjugationStatement : Prop :=
  ∀ (F D R : Type u) [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
    [Algebra.IsCentral F D] [FiniteDimensional F D] [Field R] [Algebra F R]
    (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
    (hsym : Module.finrank F σ.symmetricSubspace = 3)
    (e : R ⊗[F] D ≃ₐ[R] Matrix (Fin 2) (Fin 2) R) (a : R ⊗[F] D),
    e ((σ.quaternionConjugation hdim hsym).baseChange R a) = (e a).adjugate

theorem quaternionicSplitConjugation : QuaternionicSplitConjugationStatement.{u} := by
  intro F D R _ _ _ _ _ _ _ _ σ hdim hsym e a
  exact σ.splitQuaternionConjugation_eq_adjugate hdim hsym e a

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
