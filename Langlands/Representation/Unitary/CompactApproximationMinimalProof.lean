import Langlands.Representation.Unitary.CompactApproximationMinimalStatement
import Langlands.Analysis.CompactApproximationEigenspaceProof
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Nat.Find

noncomputable section

namespace Langlands.Analysis

universe uG uE

theorem compactApproximationMinimal :
    CompactApproximationMinimalStatement.{uG, uE} := by
  classical
  intro G _ E _ _ _ π hunit T hcompact hsymm hlim hpres W hWne hWclosed hWinv
  obtain ⟨n, μ, hμ0, hWF, _⟩ :=
    compactApproximationEigenspace E T hcompact hsymm hlim W hWne hWclosed
      (fun n => hpres n W hWclosed hWinv)
  let F : Submodule ℂ E := Module.End.eigenspace (T n).toLinearMap μ
  have : FiniteDimensional ℂ F :=
    ContinuousLinearMap.finite_dimensional_eigenspace (hcompact n) μ hμ0
  let Good : Submodule ℂ E → Prop := fun U =>
    U ≤ W ∧ IsClosed (U : Set E) ∧
      (∀ (g : G), ∀ z ∈ U, π g z ∈ U) ∧ U ⊓ F ≠ ⊥
  have hex : ∃ d : ℕ, ∃ U : Submodule ℂ E,
      Good U ∧ Module.finrank ℂ (U ⊓ F : Submodule ℂ E) = d :=
    ⟨_, W, ⟨le_rfl, hWclosed, hWinv, hWF⟩, rfl⟩
  obtain ⟨U, hU, hdU⟩ := Nat.find_spec hex
  have hUmin (V : Submodule ℂ E) (hV : Good V) :
      Module.finrank ℂ (U ⊓ F : Submodule ℂ E) ≤
        Module.finrank ℂ (V ⊓ F : Submodule ℂ E) := by
    rw [hdU]
    exact Nat.find_min' hex ⟨V, hV, rfl⟩
  rcases hU with ⟨hUW, hUclosed, hUinv, hUne⟩
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
  let S : Submodule ℂ E := Submodule.span ℂ (Set.range fun g : G => π g x)
  let P : Submodule ℂ E := S.topologicalClosure
  have hPclosed : IsClosed (P : Set E) := S.isClosed_topologicalClosure
  have horbit (g : G) : π g x ∈ P :=
    S.le_topologicalClosure (Submodule.subset_span ⟨g, rfl⟩)
  have hxP : x ∈ P := by simpa using horbit 1
  have hPmin (V : Submodule ℂ E) (hVc : IsClosed (V : Set E))
      (hVi : ∀ (g : G), ∀ z ∈ V, π g z ∈ V) (hxV : x ∈ V) : P ≤ V := by
    apply S.topologicalClosure_minimal _ hVc
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact hVi g x hxV
  have hPinv : ∀ (g : G), ∀ z ∈ P, π g z ∈ P := by
    intro g z hz
    have hle : S ≤ P.comap (π g).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨h, rfl⟩
      change (π g * π h) x ∈ P
      rw [← map_mul]
      exact horbit (g * h)
    exact S.topologicalClosure_minimal hle (hPclosed.preimage (π g).continuous) hz
  have hPU : P ≤ U := hPmin U hUclosed hUinv hx.1
  have hPW : P ≤ W := hPU.trans hUW
  refine ⟨P, hPW, ?_, hPclosed, hPinv, ?_⟩
  · intro hP
    exact hx0 ((Submodule.mem_bot ℂ).mp (hP ▸ hxP))
  · intro Q hQP hQc hQi
    have : IsClosed (Q : Set E) := hQc
    have hinv (g : G) (z : E) : π g (π g⁻¹ z) = z := by
      change (π g * π g⁻¹) z = z
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    have horthinv : ∀ (g : G), ∀ z ∈ Qᗮ, π g z ∈ Qᗮ := by
      intro g z hz y hy
      rw [← hinv g y, hunit]
      exact hz _ (hQi g⁻¹ y hy)
    have hcomm (z : E) : Q.starProjection (T n z) = T n (Q.starProjection z) := by
      apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
        (hpres n Q hQc hQi _ (Q.starProjection_apply_mem z))
      intro y hy
      rw [← (T n).map_sub]
      exact (hsymm n _ _).trans (Submodule.starProjection_inner_eq_zero z _
        (hpres n Q hQc hQi y hy))
    by_cases hqx : Q.starProjection x = 0
    · left
      have hxorth : x ∈ Qᗮ := by
        simpa only [hqx, sub_zero] using
          (Submodule.sub_starProjection_mem_orthogonal (K := Q) x)
      have hPorth : P ≤ Qᗮ := hPmin Qᗮ Q.isClosed_orthogonal horthinv hxorth
      apply le_antisymm _ bot_le
      have hle : Q ≤ Q ⊓ Qᗮ := le_inf le_rfl (hQP.trans hPorth)
      simpa only [Q.inf_orthogonal_eq_bot] using hle
    · right
      have hqF : Q.starProjection x ∈ F := by
        apply Module.End.mem_eigenspace_iff.mpr
        calc
          T n (Q.starProjection x) = Q.starProjection (T n x) := (hcomm x).symm
          _ = Q.starProjection (μ • x) := by
            exact congrArg Q.starProjection (Module.End.mem_eigenspace_iff.mp hx.2)
          _ = μ • Q.starProjection x := map_smul _ _ _
      have hQF : Q ⊓ F ≠ ⊥ := by
        apply (Submodule.ne_bot_iff _).mpr
        exact ⟨Q.starProjection x, ⟨Q.starProjection_apply_mem x, hqF⟩, hqx⟩
      have hQGood : Good Q :=
        ⟨hQP.trans hPW, hQc, hQi, hQF⟩
      have : FiniteDimensional ℂ (U ⊓ F : Submodule ℂ E) :=
        Submodule.finiteDimensional_of_le inf_le_right
      have hQUF : Q ⊓ F = U ⊓ F :=
        Submodule.eq_of_le_of_finrank_le
          (inf_le_inf (hQP.trans hPU) le_rfl) (hUmin Q hQGood)
      have hxQ : x ∈ Q := (show x ∈ Q ⊓ F from hQUF.symm ▸ hx).1
      exact le_antisymm hQP (hPmin Q hQc hQi hxQ)

end Langlands.Analysis
