import Langlands.Global.RankinSelberg.RealStandardCompactBanachAction
import Langlands.Representation.Archimedean.SmoothDerivativeBasisTopology
import Langlands.Representation.Archimedean.SmoothDerivativeCompleteness
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Topology.Baire.CompleteMetrizable

/-! # Continuity of entire normalized evaluations on smooth real standard modules -/

noncomputable section

open Filter Set Topology TopologicalSpace
open scoped ContDiff Matrix.Norms.Operator Topology Uniformity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace Langlands.Global.RankinSelbergGlobal.RealSmoothNormalizedEvaluationContinuity

section Entire

variable {E : Type*} [UniformSpace E] [AddCommGroup E] [IsUniformAddGroup E]
  [Module ℂ E] [ContinuousSMul ℂ E] [BarrelledSpace ℂ E]

private theorem exists_continuous_iteratedEval (F : E →ₗ[ℂ] (ℂ → ℂ))
    (hF : ∀ v, Differentiable ℂ (F v)) {U : Set ℂ} (hU : IsOpen U)
    (hEval : ∀ z ∈ U, Continuous (fun v => F v z)) :
    ∀ (n : ℕ) (z : ℂ), z ∈ U → ∃ L : E →L[ℂ] ℂ,
      ∀ v, L v = iteratedDeriv n (F v) z := by
  classical
  intro n
  induction n with
  | zero =>
    intro z hz
    exact ⟨⟨(LinearMap.proj z).comp F, hEval z hz⟩, fun v => by rw [iteratedDeriv_zero]; rfl⟩
  | succ n ih =>
    choose L hL using ih
    intro z hz
    let A (w : ℂ) : E →L[ℂ] ℂ :=
      if hw : w ∈ U then (w - z)⁻¹ • (L w hw - L z hz) else 0
    have hMem : ∀ᶠ w in 𝓝[≠] z, w ∈ U :=
      (hU.mem_nhds hz : U ∈ 𝓝 z) |> mem_nhdsWithin_of_mem_nhds
    have hT : Tendsto (fun w v => A w v) (𝓝[≠] z)
        (𝓝 (fun v => iteratedDeriv (n + 1) (F v) z)) := by
      apply tendsto_pi_nhds.mpr
      intro v
      have hs : ContDiff ℂ (n + 1 : ℕ) (F v) := (hF v).contDiff
      have hd : Differentiable ℂ (iteratedDeriv n (F v)) :=
        hs.differentiable_iteratedDeriv' n
      rw [iteratedDeriv_succ]
      apply ((hd z).hasDerivAt.tendsto_slope).congr'
      filter_upwards [hMem] with w hw
      simp only [A, dite_eq_left hw, smul_apply, sub_apply, hL, slope, vsub_eq_sub]
    exact ⟨continuousLinearMapOfTendsto A hT, fun _ => rfl⟩

/-- Continuity of the scalar evaluations of an entire linear family on one nonempty open
set implies continuity of each evaluation, for a barrelled source. -/
theorem continuous_eval_of_entire (F : E →ₗ[ℂ] (ℂ → ℂ))
    (hF : ∀ v, Differentiable ℂ (F v)) {U : Set ℂ} (hU : IsOpen U) (hU₀ : U.Nonempty)
    (hEval : ∀ z ∈ U, Continuous (fun v => F v z)) (s : ℂ) : Continuous (fun v => F v s) := by
  obtain ⟨z, hz⟩ := hU₀
  choose D hD using fun n => exists_continuous_iteratedEval F hF hU hEval n z hz
  let A (m : ℕ) : E →L[ℂ] ℂ :=
    ∑ n ∈ Finset.range m, (n.factorial : ℂ)⁻¹ • (s - z) ^ n • D n
  have hT : Tendsto (fun m v => A m v) atTop (𝓝 (fun v => F v s)) := by
    apply tendsto_pi_nhds.mpr
    intro v
    simpa only [A, sum_apply, smul_apply, hD]
      using (Complex.hasSum_taylorSeries_of_entire (hF v) z s).tendsto_sum_nat
  exact (continuousLinearMapOfTendsto A hT).continuous

end Entire

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open RealStandardCompactBanach

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

local notation "D[" n "," ds "]" =>
  DerivativeSmoothVectors (matrixModel ℝ n) (representation (n := n) ds)

/-- The genuine smooth derivative topology for a real standard module is a Baire topology. -/
theorem baireSpace_realStandardSmooth (n : ℕ) (ds : List RealBlock) : BaireSpace D[n,ds] := by
  let : CompleteSpace D[n,ds] := DerivativeSmoothVectors.completeSpace_of_isContinuousRepresentation_units
    (representation (n := n) ds) (isContinuousRepresentation ds)
  let : MetrizableSpace D[n,ds] := DerivativeSmoothVectors.metrizableSpace_of_finiteDimensional
    (matrixModel ℝ n) (representation (n := n) ds)
  let : (𝓤 D[n,ds]).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero]
    infer_instance
  infer_instance

/-- An entire linear normalization on smooth real standard vectors has continuous
spectral evaluations as soon as these are continuous on a nonempty open set. -/
def RealSmoothNormalizedEvaluationContinuityStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock) (F : D[n,ds] →ₗ[ℂ] (ℂ → ℂ)),
    (∀ v, Differentiable ℂ (F v)) →
    ∀ (U : Set ℂ), IsOpen U → U.Nonempty →
      (∀ z ∈ U, Continuous (fun v => F v z)) → ∀ s, Continuous (fun v => F v s)

theorem realSmoothNormalizedEvaluationContinuity : RealSmoothNormalizedEvaluationContinuityStatement := by
  intro n ds F hF U hU hU₀ hEval s
  let : BaireSpace D[n,ds] := baireSpace_realStandardSmooth n ds
  exact continuous_eval_of_entire F hF hU hU₀ hEval s

end Langlands.Global.RankinSelbergGlobal.RealSmoothNormalizedEvaluationContinuity
