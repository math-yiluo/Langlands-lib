import Langlands.Analysis.CompactApproximationEigenspaceStatement

open Filter
open scoped Topology

namespace Langlands.Analysis

universe u

/-- The first eigenspace step for a strongly convergent compact symmetric
approximation to the identity. -/
theorem compactApproximationEigenspace :
    CompactApproximationEigenspaceStatement.{u} := by
  intro E _ _ _ T hcompact hsymm hlim W hWne hWclosed hinv
  have : CompleteSpace W := hWclosed.completeSpace_coe
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
  have hn : ∃ n, T n x ≠ 0 := by
    by_contra! hz
    have hzero : Tendsto (fun _ : ℕ => (0 : E)) atTop (𝓝 x) := by
      simpa only [hz] using hlim x
    exact hx0 (tendsto_nhds_unique hzero tendsto_const_nhds)
  obtain ⟨n, hnx⟩ := hn
  let S : W →L[ℂ] W := (T n).restrict (hinv n)
  have hS0 : S ≠ 0 := by
    intro h
    apply hnx
    exact congrArg (fun f : W →L[ℂ] W => (f ⟨x, hxW⟩ : E)) h
  have hSc : IsCompactOperator S := (hcompact n).restrict' (hinv n)
  have hSs : S.IsSymmetric := (hsymm n).restrict_invariant (hinv n)
  have hμ : ∃ μ : ℂ, Module.End.HasEigenvalue S.toLinearMap μ ∧ μ ≠ 0 := by
    by_contra! h
    exact hS0 ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hSc hSs).mp h)
  obtain ⟨μ, hμ, hμ0⟩ := hμ
  obtain ⟨y, hy⟩ := hμ.exists_hasEigenvector
  refine ⟨n, μ, hμ0, ?_, ?_⟩
  · apply (Submodule.ne_bot_iff _).mpr
    refine ⟨(y : E), ⟨y.property, ?_⟩, ?_⟩
    · apply Module.End.mem_eigenspace_iff.mpr
      exact congrArg (fun z : W => (z : E)) hy.apply_eq_smul
    · intro h
      exact hy.2 (Subtype.ext h)
  · have : FiniteDimensional ℂ (Module.End.eigenspace (T n).toLinearMap μ) :=
      ContinuousLinearMap.finite_dimensional_eigenspace (hcompact n) μ hμ0
    exact Submodule.finiteDimensional_of_le inf_le_right

end Langlands.Analysis
