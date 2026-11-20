import Langlands.LinearAlgebra.MatrixTransposeConjugateProof
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Simultaneous transposition when a commuting matrix is cyclic -/

noncomputable section

open Polynomial Matrix

set_option autoImplicit false

namespace Langlands

variable {k : Type*} [Field k] {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) k

/-- The columns of the cyclic vector matrix are the first `n` iterates of the supplied vector. -/
def cyclicVectorMatrix (T : Mat) (v : Fin n → k) : Mat := fun i j => (T ^ (j : ℕ) *ᵥ v) i

/-- A matrix has a cyclic vector when these iterates form a basis. -/
def HasCyclicMatrixVector (T : Mat) : Prop := ∃ v, (cyclicVectorMatrix T v).det ≠ 0

/-- A nonsingular cyclic vector matrix makes evaluation on that vector surjective. -/
theorem exists_aeval_mulVec_of_cyclicVectorMatrix (T : Mat) (v : Fin n → k)
    (hv : (cyclicVectorMatrix T v).det ≠ 0) (w : Fin n → k) :
    ∃ p : k[X], aeval T p *ᵥ v = w := by
  have hu : IsUnit (cyclicVectorMatrix T v) :=
    (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hv)
  obtain ⟨c, hc⟩ := (mulVec_surjective_iff_isUnit.mpr hu) w
  refine ⟨∑ i : Fin n, monomial (i : ℕ) (c i), ?_⟩
  simp only [map_sum, aeval_monomial, ← Algebra.smul_def, sum_mulVec, smul_mulVec]
  rw [← hc]
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, mulVec, dotProduct, cyclicVectorMatrix, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem semiconjBy_aeval_matrix {A T U : Mat} (h : SemiconjBy A T U) (p : k[X]) :
    SemiconjBy A (aeval T p) (aeval U p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [map_add] using hp.add_right hq
  | monomial d c =>
      rw [aeval_monomial, aeval_monomial]
      have hr : Commute A (algebraMap k Mat c) := (Algebra.commutes c A).symm
      exact SemiconjBy.mul_right hr (h.pow_right d)

/-- Every matrix commuting with a cyclic matrix is a polynomial in it. -/
theorem exists_aeval_eq_of_commute_of_cyclic {T U : Mat}
    (hT : HasCyclicMatrixVector T) (h : Commute U T) : ∃ p : k[X], aeval T p = U := by
  obtain ⟨v, hv⟩ := hT
  obtain ⟨p, hp⟩ := exists_aeval_mulVec_of_cyclicVectorMatrix T v hv (U *ᵥ v)
  refine ⟨p, Matrix.mulVec_injective (funext fun x => ?_)⟩
  obtain ⟨q, rfl⟩ := exists_aeval_mulVec_of_cyclicVectorMatrix T v hv x
  have hc := semiconjBy_aeval_matrix h q
  rw [mulVec_mulVec, mulVec_mulVec, hc.eq, ← map_mul, mul_comm p q, map_mul,
    ← mulVec_mulVec, hp, mulVec_mulVec]

/-- Transpose commutes with polynomial evaluation in a single matrix. -/
theorem transpose_aeval_matrix (T : Mat) (p : k[X]) : (aeval T p)ᵀ = aeval Tᵀ p := by
  apply MulOpposite.op_injective
  have h := (aeval_algHom_apply (Matrix.transposeAlgEquiv (m := Fin n) (R := k) (α := k)) T p).symm
  change MulOpposite.op (aeval T p)ᵀ = aeval (MulOpposite.op Tᵀ) p at h
  rw [h, aeval_op_apply]

/-- The same invertible matrix conjugates a commuting pair to its two transposes when a
cyclic member of the pair generates its commutant. -/
theorem exists_simultaneous_transpose_conjugator_of_cyclic {T U : Mat}
    (hT : HasCyclicMatrixVector T) (h : Commute U T) :
    ∃ a : Matˣ, a.val * T * a.inv = Tᵀ ∧ a.val * U * a.inv = Uᵀ := by
  obtain ⟨p, rfl⟩ := exists_aeval_eq_of_commute_of_cyclic hT h
  obtain ⟨a, ha⟩ := matrixTransposeConjugate k n T
  have hT' : SemiconjBy a.val T Tᵀ := by
    change a.val * T = Tᵀ * a.val
    have hh : (↑a⁻¹ : Mat) * (↑a : Mat) = 1 := a.inv_val
    rw [← ha, mul_assoc (a.val * T), hh, mul_one]
  have hp := semiconjBy_aeval_matrix hT' p
  refine ⟨a, ha, ?_⟩
  rw [transpose_aeval_matrix, hp.eq, mul_assoc, a.val_inv, mul_one]

end Langlands
