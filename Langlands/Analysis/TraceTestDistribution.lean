import Langlands.Analysis.CompactTestCompleteness
import Langlands.Analysis.OperatorTraceProof
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.LocallyConvex.Barrelled

/-! # Distributional traces of weakly continuous trace-class test operators -/

noncomputable section

open Filter Set TopologicalSpace Bornology
open scoped BigOperators Distributions InnerProductSpace Topology

set_option autoImplicit false

namespace Langlands.Analysis.OperatorIdeals

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Ω : Opens E}
  (T : 𝓓(Ω, ℝ) →ₗ[ℝ] H →L[ℂ] H)
  (hT : ∀ φ, IsTraceClass (T φ))
  (hcoeff : ∀ x : H, Continuous (fun φ : 𝓓(Ω, ℝ) => ⟪x, T φ x⟫_ℂ))

include hT hcoeff in
private theorem continuous_trace_on_compactTests (K : Compacts E) (hK : (K : Set E) ⊆ Ω) :
    Continuous (fun φ : 𝓓_{K}(E, ℝ) => operatorTrace (T (TestFunction.ofSupportedIn hK φ))) := by
  classical
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis ℂ H
  let : BaireSpace 𝓓_{K}(E, ℝ) := baireSpace_compactSmoothTests K
  let d (i : ι) : 𝓓_{K}(E, ℝ) →L[ℝ] ℂ :=
    { toFun := fun φ => ⟪b i, T (TestFunction.ofSupportedIn hK φ) (b i)⟫_ℂ
      map_add' := by
        intro φ ψ
        change ⟪b i, T (TestFunction.ofSupportedInCLM ℝ hK (φ + ψ)) (b i)⟫_ℂ = _
        rw [map_add, map_add, add_apply, inner_add_right]
        rfl
      map_smul' := by
        intro c φ
        change ⟪b i, T (TestFunction.ofSupportedInCLM ℝ hK (c • φ)) (b i)⟫_ℂ = _
        rw [map_smul, map_smul]
        change ⟪b i, (c : ℂ) • T (TestFunction.ofSupportedIn hK φ) (b i)⟫_ℂ =
          c • ⟪b i, T (TestFunction.ofSupportedIn hK φ) (b i)⟫_ℂ
        exact inner_smul_real_right _ _ _
      cont := (hcoeff (b i)).comp (TestFunction.ofSupportedInCLM ℝ hK).continuous }
  let p (s : Finset ι) : 𝓓_{K}(E, ℝ) →L[ℝ] ℂ := ∑ i ∈ s, d i
  have hp (s : Finset ι) (φ : 𝓓_{K}(E, ℝ)) :
      p s φ = ∑ i ∈ s, d i φ := by simp [p]
  have hs (φ : 𝓓_{K}(E, ℝ)) :
      Summable (fun i : ι => ‖d i φ‖) ∧
        operatorTrace (T (TestFunction.ofSupportedIn hK φ)) = ∑' i : ι, d i φ :=
    operatorTraceBasis H _ ι b (hT _)
  have hBound (φ : 𝓓_{K}(E, ℝ)) :
      IsVonNBounded ℝ (Set.range (fun s : Finset ι => p s φ)) := by
    apply NormedSpace.isVonNBounded_of_isBounded
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨∑' i : ι, ‖d i φ‖, ?_⟩
    rintro _ ⟨s, rfl⟩
    change ‖p s φ‖ ≤ _
    rw [hp]
    exact (norm_sum_le _ _).trans ((hs φ).1.sum_le_tsum s (fun i _ => norm_nonneg (d i φ)))
  have hlim : Tendsto (fun s φ => p s φ) atTop
      (𝓝 fun φ => operatorTrace (T (TestFunction.ofSupportedIn hK φ))) := by
    rw [tendsto_pi_nhds]
    intro φ
    simpa only [hp, (hs φ).2, HasSum, SummationFilter.unconditional_filter]
      using (hs φ).1.of_norm.hasSum
  exact hlim.continuous_of_equicontinuous
    (PolynormableSpace.banach_steinhaus (𝓕 := p) hBound).equicontinuous

/-- A real-linear family of trace-class test operators with continuous diagonal matrix
coefficients defines a complex-valued distribution by taking the operator trace. -/
def traceTestDistribution : 𝓓'(Ω, ℂ) :=
  TestFunction.mkCLM ℝ (fun φ => operatorTrace (T φ))
    (by
      intro φ ψ
      rw [map_add, operatorTrace_add _ _ (hT φ) (hT ψ)])
    (by
      intro c φ
      rw [map_smul]
      change operatorTrace ((c : ℂ) • T φ) = c • operatorTrace (T φ)
      exact operatorTrace_smul c (T φ) (hT φ))
    (continuous_trace_on_compactTests T hT hcoeff)

@[simp]
theorem traceTestDistribution_apply (φ : 𝓓(Ω, ℝ)) :
    traceTestDistribution T hT hcoeff φ = operatorTrace (T φ) := rfl

end Langlands.Analysis.OperatorIdeals
