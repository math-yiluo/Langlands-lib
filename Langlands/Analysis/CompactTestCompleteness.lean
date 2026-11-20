import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Topology.Baire.CompleteMetrizable

/-! # Completeness of the space of smooth functions supported in a fixed compact set -/

noncomputable section

open Filter Function Set TopologicalSpace
open scoped BoundedContinuousFunction ContDiff Distributions Topology

set_option autoImplicit false

namespace Langlands.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Compacts E)

open ContDiffMapSupportedIn (structureMapCLM)

/-- The derivative coordinates of a smooth test at a fixed compact support,
each bundled as a bounded continuous function. -/
def compactSmoothTestDerivatives :
    𝓓_{K}(E, F) →L[ℝ] (∀ i : ℕ, E →ᵇ (E [×i]→L[ℝ] F)) :=
  ContinuousLinearMap.pi (structureMapCLM ℝ ⊤)

private theorem isClosed_range_compactTestDerivatives :
    IsClosed (Set.range (compactSmoothTestDerivatives (F := F) K)) := by
  classical
  let J := compactSmoothTestDerivatives (F := F) K
  change IsClosed (Set.range J)
  rw [← isSeqClosed_iff_isClosed]
  intro u y hu hy
  choose f hf using hu
  have hJ (m : ℕ) (i : ℕ) :
      (u m i : E → E [×i]→L[ℝ] F) = iteratedFDeriv ℝ i (f m) := by
    rw [← hf m]
    exact ContDiffMapSupportedIn.structureMapCLM_top_apply ℝ (f m)
  have hUniform (i : ℕ) :
      TendstoUniformly (fun m => iteratedFDeriv ℝ i (f m)) (y i) atTop := by
    have h := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      ((continuous_apply i).continuousAt.tendsto.comp hy)
    simpa only [Function.comp_def, hJ] using h
  have hD (i : ℕ) (x : E) : HasFDerivAt (y i : E → E [×i]→L[ℝ] F)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => E) F (y (i + 1) x)) x := by
    let c := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => E) F
    have hu' := c.isometry.uniformContinuous.comp_tendstoUniformly (hUniform (i + 1))
    apply hasFDerivAt_of_tendstoUniformly hu' ?_ (fun z => (hUniform i).tendsto_at z) x
    intro m z
    have hd : Differentiable ℝ (iteratedFDeriv ℝ i (f m)) :=
      (contDiff_infty.mp (f m).contDiff (i + 1)).differentiable_iteratedFDeriv
        (mod_cast Nat.lt_succ_self i)
    change HasFDerivAt (iteratedFDeriv ℝ i (f m))
      (fderiv ℝ (iteratedFDeriv ℝ i (f m)) z) z
    exact (hd z).hasFDerivAt
  let c₀ := continuousMultilinearCurryFin0 ℝ E F
  let g : E → F := fun x => c₀ (y 0 x)
  have he (i : ℕ) : iteratedFDeriv ℝ i g = (y i : E → E [×i]→L[ℝ] F) := by
    induction i with
    | zero =>
      rw [iteratedFDeriv_zero_eq_comp]
      funext x
      exact c₀.symm_apply_apply (y 0 x)
    | succ i ih =>
      rw [iteratedFDeriv_succ_eq_comp_left, ih]
      funext x
      rw [Function.comp_apply, (hD i x).fderiv]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => E) F).symm_apply_apply _
  have hSmooth : ContDiff ℝ ∞ g := by
    apply contDiff_of_differentiable_iteratedFDeriv
    intro i _
    rw [he]
    exact fun x => (hD i x).differentiableAt
  have hSupport : EqOn g 0 (K : Set E)ᶜ := by
    intro x hx
    have ht := (c₀.continuous.tendsto (y 0 x)).comp ((hUniform 0).tendsto_at x)
    have hzero (m : ℕ) : c₀ (iteratedFDeriv ℝ 0 (f m) x) = 0 := by
      rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, c₀.apply_symm_apply]
      exact (f m).zero_on_compl hx
    have hg : Tendsto (fun _ : ℕ => (0 : F)) atTop (𝓝 (g x)) := by
      simpa only [Function.comp_def, hzero, g] using ht
    exact tendsto_nhds_unique hg tendsto_const_nhds
  let φ : 𝓓_{K}(E, F) := ⟨g, hSmooth, hSupport⟩
  refine ⟨φ, funext fun i => BoundedContinuousFunction.ext fun x => ?_⟩
  change structureMapCLM ℝ ⊤ i φ x = y i x
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply, show (φ : E → F) = g from rfl, he]

variable [CompleteSpace F]

/-- The space of smooth functions supported in a fixed compact set is complete for
the uniformity of uniform convergence of every iterated derivative. -/
theorem completeSpace_compactSmoothTests : CompleteSpace 𝓓_{K}(E, F) :=
  (ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM ℝ (n := ⊤)
    (K := K)).isUniformInducing.completeSpace (isClosed_range_compactTestDerivatives K).isComplete

/-- The space of smooth functions supported in a fixed compact set is a Baire space. -/
theorem baireSpace_compactSmoothTests : BaireSpace 𝓓_{K}(E, F) := by
  have h := ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM ℝ
    (E := E) (F := F) (n := ⊤) (K := K)
  let : IsCompletelyPseudoMetrizableSpace 𝓓_{K}(E, F) :=
    Topology.IsClosedEmbedding.IsCompletelyPseudoMetrizableSpace
      ⟨h.isEmbedding, isClosed_range_compactTestDerivatives K⟩
  infer_instance

end Langlands.Analysis
