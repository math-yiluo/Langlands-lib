import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # The conormal of matrix conjugation via the trace form -/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands

variable {k : Type*} [Field k] {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) k

/-- The bilinear form `(A, B) ↦ tr(A * B)` on square matrices. -/
def matrixTraceBilin : LinearMap.BilinForm k Mat :=
  LinearMap.mk₂ k (fun A B => trace (A * B))
    (fun A B X => by rw [add_mul, trace_add])
    (fun a A X => by rw [smul_mul_assoc, trace_smul])
    (fun X A B => by rw [mul_add, trace_add])
    (fun a X A => by rw [mul_smul_comm, trace_smul])

@[simp]
theorem matrixTraceBilin_apply (A B : Mat) :
    matrixTraceBilin A B = trace (A * B) := rfl

theorem matrixTraceBilin_isSymm :
    (matrixTraceBilin : LinearMap.BilinForm k Mat).IsSymm :=
  ⟨fun A B => trace_mul_comm A B⟩

theorem matrixTraceBilin_nondegenerate :
    (matrixTraceBilin : LinearMap.BilinForm k Mat).Nondegenerate := by
  constructor
  · intro A hA
    apply ext_iff_trace_mul_right.mpr
    intro X
    simpa only [matrixTraceBilin_apply, zero_mul, trace_zero] using hA X
  · intro A hA
    apply ext_iff_trace_mul_left.mpr
    intro X
    simpa only [matrixTraceBilin_apply, mul_zero, trace_zero] using hA X

/-- The infinitesimal conjugation map at `C`. -/
def matrixConjugationTangent (C : Mat) : Mat →ₗ[k] Mat :=
  LinearMap.mulRight k C - LinearMap.mulLeft k C

@[simp]
theorem matrixConjugationTangent_apply (C X : Mat) :
    matrixConjugationTangent C X = X * C - C * X := rfl

theorem matrixTraceBilin_conjugationTangent (C X A : Mat) :
    matrixTraceBilin (matrixConjugationTangent C X) A =
      matrixTraceBilin X (C * A - A * C) := by
  simp only [matrixTraceBilin_apply, matrixConjugationTangent_apply, sub_mul, mul_sub, trace_sub]
  rw [mul_assoc X C A, mul_assoc C X A, trace_mul_comm C (X * A), mul_assoc X A C]

/-- The trace annihilator of the image of infinitesimal conjugation is the matrix
centralizer of the base point. -/
theorem mem_matrixTraceBilin_orthogonal_conjugationTangent_iff (C A : Mat) :
    A ∈ matrixTraceBilin.orthogonal (LinearMap.range (matrixConjugationTangent C)) ↔
      Commute C A := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    have hz : C * A - A * C = 0 :=
      matrixTraceBilin_nondegenerate.2 (C * A - A * C) fun X => by
        rw [← matrixTraceBilin_conjugationTangent]
        exact h _ ⟨X, rfl⟩
    exact sub_eq_zero.mp hz
  · intro h Y hY
    obtain ⟨X, rfl⟩ := hY
    rw [matrixTraceBilin_conjugationTangent, h.eq, sub_self, map_zero]

theorem matrixTraceBilin_units_conj (q : Matˣ) (A B : Mat) :
    matrixTraceBilin (q.val * A * q.inv) (q.val * B * q.inv) =
      matrixTraceBilin A B := by
  rw [matrixTraceBilin_apply, matrixTraceBilin_apply]
  have h : (q.val * A * q.inv) * (q.val * B * q.inv) = q.val * (A * B) * q.inv := by
    simp [mul_assoc]
  rw [h]
  exact trace_units_conj q (A * B)

theorem matrixTraceBilin_transpose (A B : Mat) :
    matrixTraceBilin Aᵀ Bᵀ = matrixTraceBilin A B :=
  trace_transpose_mul A B

/-- The trace form identifies the annihilator written as a subspace of matrices
with the dual of a quotient by the proposed tangent subspace. -/
def matrixTraceOrthogonalEquivDualQuotient (W : Submodule k Mat) :
    ↥(matrixTraceBilin.orthogonal W) ≃ₗ[k] Module.Dual k (Mat ⧸ W) := by
  let T := (matrixTraceBilin : LinearMap.BilinForm k Mat).toDual matrixTraceBilin_nondegenerate
  refine (T.ofSubmodules _ W.dualAnnihilator ?_).trans W.dualQuotEquivDualAnnihilator.symm
  ext f
  change f ∈ (matrixTraceBilin.orthogonal W).map T.toLinearMap ↔ f ∈ W.dualAnnihilator
  rw [Submodule.mem_map_equiv, LinearMap.BilinForm.mem_orthogonal_iff,
    Submodule.mem_dualAnnihilator]
  refine forall_congr' fun X => imp_congr_right fun _ => ?_
  rw [matrixTraceBilin_isSymm.eq X (T.symm f)]
  change T (T.symm f) X = 0 ↔ f X = 0
  rw [T.apply_symm_apply]

@[simp]
theorem matrixTraceOrthogonalEquivDualQuotient_apply_mk (W : Submodule k Mat)
    (A : matrixTraceBilin.orthogonal W) (X : Mat) :
    matrixTraceOrthogonalEquivDualQuotient W A (Submodule.Quotient.mk X) =
      matrixTraceBilin A.val X := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Differentiating actual exponential conjugation computes the infinitesimal conjugation map. -/
theorem hasDerivAt_matrixExponential_conj (C X : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt
      (fun t : ℝ => NormedSpace.exp (t • X) * C * NormedSpace.exp (t • (-X)))
      (matrixConjugationTangent C X) 0 := by
  have h₁ := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)).mul_const C
  have h₂ := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) (0 : ℝ)
  simpa [sub_eq_add_neg] using h₁.fun_mul h₂

end Langlands
