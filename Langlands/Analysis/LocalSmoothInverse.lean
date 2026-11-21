import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! # Smooth inverse on an open chart -/

noncomputable section
set_option autoImplicit false

open Set
open scoped ContDiff

namespace Langlands.Analysis

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A globally smooth map with invertible derivative at a point admits
an open partial homeomorphism there with smooth inverse on the target. -/
theorem exists_localSmoothInverse {f : E → F} {x : E} {L : E ≃L[ℝ] F}
    (hf : ContDiff ℝ ∞ f) (hL : HasFDerivAt f (L : E →L[ℝ] F) x) :
    ∃ e : OpenPartialHomeomorph E F,
      (e : E → F) = f ∧ x ∈ e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let h := hf.contDiffAt (x := x)
  let e := h.toOpenPartialHomeomorph f hL (by simp)
  let S : Set E := fderiv ℝ f ⁻¹' range ((↑) : (E ≃L[ℝ] F) → E →L[ℝ] F)
  have hS : IsOpen S :=
    ContinuousLinearEquiv.isOpen.preimage (hf.continuous_fderiv (by simp))
  let e' := e.restrOpen S hS
  have he' : (e' : E → F) = f := rfl
  refine ⟨e', he', ⟨h.mem_toOpenPartialHomeomorph_source hL (by simp), ?_⟩, ?_⟩
  · change fderiv ℝ f x ∈ range ((↑) : (E ≃L[ℝ] F) → E →L[ℝ] F)
    rw [hL.fderiv]
    exact mem_range_self L
  · intro y hy
    have hs : fderiv ℝ f (e'.symm y) ∈ range ((↑) : (E ≃L[ℝ] F) → E →L[ℝ] F) :=
      (e'.map_target hy).2
    obtain ⟨d, hd⟩ := hs
    apply (e'.contDiffAt_symm hy (f₀' := d) ?_ ?_).contDiffWithinAt
    · rw [he', hd]
      exact (hf.differentiable (by simp) _).hasFDerivAt
    · rw [he']
      exact hf.contDiffAt

end Langlands.Analysis
