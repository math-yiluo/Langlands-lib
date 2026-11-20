import Langlands.Global.ArchimedeanSmoothFamily
import Langlands.Global.ArchimedeanNormedDerivativeCoordinates
import Langlands.Global.ArchimedeanCompactIndexDerivatives
import Langlands.Analysis.ComplexSubmoduleClosure

/-! # Compact averages of simultaneous right translations -/

noncomputable section
universe u w
open Filter Topology TopologicalSpace MeasureTheory
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL.SmoothFamily

open DerivativeSmoothFunctions

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} {ι : Type w}

private abbrev Coordinate (F : Type u) [Field F] [NumberField F] (n : ℕ) :=
  EnvelopingAlgebra F n × Compacts (InfiniteAdelicGL F n)

private def normedCoordinates : SmoothFamily F n ι →L[ℝ]
    (∀ i : ι × Coordinate F n, C(i.2.2, ℂ)) :=
  ContinuousLinearMap.pi fun i =>
    ((ContinuousLinearMap.proj i.2).comp (normedDerivativeCoordinates F n)).comp
      (ContinuousLinearMap.proj i.1)

private theorem normedCoordinates_apply (f : SmoothFamily F n ι) (i : ι × Coordinate F n)
    (x : i.2.2) :
    normedCoordinates f i x = (envelopingAction F n i.2.1 (toSmooth F n (f i.1))).val x :=
  normedDerivativeCoordinates_apply F n (f i.1) i.2.1 i.2.2 x

private theorem isEmbedding_normedCoordinates :
    IsEmbedding (normedCoordinates (F := F) (n := n) (ι := ι)) := by
  let e := normedCoordinates (F := F) (n := n) (ι := ι)
  refine ⟨isInducing_iff_nhds.mpr (fun f => le_antisymm ?_ ?_), ?_⟩
  · exact e.continuous.continuousAt.le_comap
  · have h : Tendsto e (Filter.comap e (𝓝 (e f))) (𝓝 (e f)) := tendsto_comap
    rw [← tendsto_id']
    apply tendsto_pi_nhds.mpr
    intro i
    apply (tendsto_normedDerivativeCoordinates_iff F n).mp
    apply tendsto_pi_nhds.mpr
    intro a
    exact (tendsto_pi_nhds.mp h) (i, a)
  · intro f g h
    funext i
    apply (isEmbedding_normedDerivativeCoordinates F n).injective
    funext a
    exact congrFun h (i, a)

variable {J : Type u} [TopologicalSpace J] [T2Space J] [CompactSpace J]
  [MeasurableSpace J] [BorelSpace J]
variable (r : C(J, InfiniteAdelicGL F n)) (ν : Measure J) [IsFiniteMeasure ν] (w : C(J, ℂ))

/-- Smooth compact-index averaging of the same orbit parameter and weight in every slice. -/
def averageLM : SmoothFamily F n ι →ₗ[ℂ] SmoothFamily F n ι :=
  LinearMap.pi fun i => (CompactIndexAverage.averageLM r ν w).comp (LinearMap.proj i)

@[simp]
theorem averageLM_apply (f : SmoothFamily F n ι) (i : ι) :
    averageLM r ν w f i = CompactIndexAverage.averageLM r ν w (f i) := rfl

theorem continuous_rightRepresentation :
    Continuous (fun p : InfiniteAdelicGL F n × SmoothFamily F n ι =>
      rightRepresentation p.1 p.2) :=
  continuous_pi fun i => (continuous_rightAction F n).comp
    (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))

set_option maxHeartbeats 500000 in
/-- Continuous complex linear functionals commute with simultaneous averaging.
The integral is computed in the finitely many normed coordinates that detect the functional. -/
theorem apply_averageLM (ℓ : SmoothFamily F n ι →L[ℂ] ℂ) (f : SmoothFamily F n ι) :
    ℓ (averageLM r ν w f) = ∫ j, ℓ (w j • rightRepresentation (r j) f) ∂ν := by
  classical
  let e := normedCoordinates (F := F) (n := n) (ι := ι)
  obtain ⟨L, hL⟩ := Langlands.Analysis.continuousLinearMap_extends_product_embedding
    e isEmbedding_normedCoordinates (ℓ.restrictScalars ℝ)
  obtain ⟨I, U, hU⟩ := Langlands.Analysis.continuousLinearMap_product_factors L
  let P : SmoothFamily F n ι →L[ℝ] (∀ i : I, C(i.val.2.2, ℂ)) :=
    ContinuousLinearMap.pi fun i => (ContinuousLinearMap.proj i.val).comp e
  have hℓ (v : SmoothFamily F n ι) : ℓ v = U (P v) :=
    (hL v).symm.trans (hU (e v))
  let v : J → SmoothFamily F n ι := fun j => w j • rightRepresentation (r j) f
  have hv : Continuous v := by
    have ho : Continuous fun j : J => (r j, f) :=
      r.continuous.prodMk continuous_const
    exact w.continuous.smul (continuous_rightRepresentation.comp (f := fun j => (r j, f)) ho)
  have hP : Integrable (fun j => P (v j)) ν :=
    (P.continuous.comp hv).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hA : P (averageLM r ν w f) = ∫ j, P (v j) ∂ν := by
    funext i
    apply ContinuousMap.ext
    intro x
    let ev : (∀ i : I, C(i.val.2.2, ℂ)) →L[ℝ] ℂ :=
      (ContinuousMap.evalCLM ℝ x).comp (ContinuousLinearMap.proj i)
    change normedCoordinates (averageLM r ν w f) i.val x = ev (∫ j, P (v j) ∂ν)
    rw [← ev.integral_comp_comm hP]
    change normedCoordinates (averageLM r ν w f) i.val x =
      ∫ j, normedCoordinates (v j) i.val x ∂ν
    have hsmooth : toSmooth F n (CompactIndexAverage.averageLM r ν w (f i.val.1)) =
        CompactIndexAverage.averageSmoothLM r ν w (toSmooth F n (f i.val.1)) := by
      simp only [CompactIndexAverage.averageLM, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    simp only [normedCoordinates_apply, averageLM_apply, hsmooth, v,
      rightRepresentation_apply, map_smul, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, toSmooth_rightAction]
    exact CompactIndexAverage.envelopingDerivative_average r ν i.val.2.1 w
      (toSmooth F n (f i.val.1)) x
  change ℓ (averageLM r ν w f) = ∫ j, ℓ (v j) ∂ν
  simp only [hℓ, hA, ← U.integral_comp_comm hP]

/-- A simultaneous compact-index average lies in every closed submodule
that contains the corresponding simultaneous translates. -/
theorem averageLM_mem_topologicalClosure (S : Submodule ℂ (SmoothFamily F n ι))
    (f : SmoothFamily F n ι) (hS : ∀ j, rightRepresentation (r j) f ∈ S.topologicalClosure) :
    averageLM r ν w f ∈ S.topologicalClosure := by
  apply Langlands.Analysis.mem_topologicalClosure_of_forall_complex_annihilator
  intro ℓ hℓ
  have hc : (S.topologicalClosure : Set (SmoothFamily F n ι)) ⊆ {v | ℓ v = 0} :=
    closure_minimal hℓ (isClosed_eq ℓ.continuous continuous_const)
  rw [apply_averageLM]
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall fun j => hc (S.topologicalClosure.smul_mem _ (hS j))

end Langlands.Global.ArchimedeanGL.SmoothFamily
