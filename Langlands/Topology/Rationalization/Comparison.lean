import Langlands.Topology.Rationalization.Lattice
import Mathlib.Topology.Algebra.Ring.Basic

noncomputable section
open scoped TensorProduct
open Topology

namespace Langlands.Topology.Rationalization

variable {R B : Type*} [CommRing R] [TopologicalSpace R]
  [CommRing B] [Algebra ℚ B] [TopologicalSpace B] [IsTopologicalRing B]

private def rationalMulHomeomorph (q : ℚ) (hq : q ≠ 0) : B ≃ₜ B where
  toFun b := algebraMap ℚ B q * b
  invFun b := algebraMap ℚ B q⁻¹ * b
  left_inv b := by
    change algebraMap ℚ B q⁻¹ * (algebraMap ℚ B q * b) = b
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hq, map_one, one_mul]
  right_inv b := by
    change algebraMap ℚ B q * (algebraMap ℚ B q⁻¹ * b) = b
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hq, map_one, one_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

local instance : TopologicalSpace (ℚ ⊗[ℤ] R) := finalTopology R

/-- A normalized algebraic rationalization comparison is a homeomorphism if its
integral map is an open embedding. The rationalized source carries its final topology. -/
def comparisonHomeomorph (e : (ℚ ⊗[ℤ] R) ≃ₐ[ℚ] B) (j : R →+* B)
    (hj : IsOpenEmbedding j)
    (he : ∀ (q : ℚ) (a : R), e (q ⊗ₜ[ℤ] a) = algebraMap ℚ B q * j a) :
    (ℚ ⊗[ℤ] R) ≃ₜ B where
  toEquiv := e.toEquiv
  continuous_toFun := by
    change Continuous e
    apply continuous_of_forall_continuous_tmul
    intro q
    have hf : (fun a : R => e (q ⊗ₜ[ℤ] a)) =
        (fun _ : R => algebraMap ℚ B q) * (j : R → B) := funext (he q)
    rw [hf]
    exact continuous_const.mul hj.continuous
  continuous_invFun := by
    change Continuous e.symm
    apply continuous_iff_continuousAt.2
    intro b
    obtain ⟨q, hq, a, ha⟩ := exists_chart (e.symm b)
    have hb : e (q ⊗ₜ[ℤ] a) = b := by rw [ha, AlgEquiv.apply_symm_apply]
    rw [← hb]
    have hc : IsOpenEmbedding (fun a : R => e (q ⊗ₜ[ℤ] a)) := by
      have hf : (fun a : R => e (q ⊗ₜ[ℤ] a)) =
          (rationalMulHomeomorph (B := B) q hq) ∘ j := funext (he q)
      rw [hf]
      exact (rationalMulHomeomorph (B := B) q hq).isOpenEmbedding.comp hj
    apply (hc.continuousAt_iff (x := a)).mp
    simpa only [Function.comp_def, AlgEquiv.symm_apply_apply] using
      (Rationalization.continuous_tmul (M := R) q).continuousAt

omit [IsTopologicalRing B] in
@[simp] theorem comparisonHomeomorph_apply [IsTopologicalRing B]
    (e : (ℚ ⊗[ℤ] R) ≃ₐ[ℚ] B) (j : R →+* B)
    (hj : IsOpenEmbedding j)
    (he : ∀ (q : ℚ) (a : R), e (q ⊗ₜ[ℤ] a) = algebraMap ℚ B q * j a)
    (x : ℚ ⊗[ℤ] R) :
    comparisonHomeomorph e j hj he x = e x := rfl

omit [IsTopologicalRing B] in
@[simp] theorem comparisonHomeomorph_symm_apply [IsTopologicalRing B]
    (e : (ℚ ⊗[ℤ] R) ≃ₐ[ℚ] B) (j : R →+* B)
    (hj : IsOpenEmbedding j)
    (he : ∀ (q : ℚ) (a : R), e (q ⊗ₜ[ℤ] a) = algebraMap ℚ B q * j a)
    (b : B) :
    (comparisonHomeomorph e j hj he).symm b = e.symm b := rfl

end Langlands.Topology.Rationalization
