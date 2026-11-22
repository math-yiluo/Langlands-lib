import Langlands.Analysis.CompactManifoldVectorIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Compact manifold integrals with an integrable scalar weight -/

noncomputable section
set_option autoImplicit false

universe uX uV uM uH uN uE

open MeasureTheory Set
open scoped ContDiff ENNReal Manifold

namespace Langlands.Analysis

/-- A jointly smooth manifold kernel integrated against a measurable integrable weight
on a compact space is smooth, with derivative given by the integrated derivative. -/
def CompactManifoldIntegrableWeightStatement : Prop :=
  ∀ (X : Type uX) [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (V : Type uV) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (M : Type uM) [TopologicalSpace M] [ChartedSpace V M] [IsManifold 𝓘(ℝ, V) ∞ M]
    (H : Type uH) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (N : Type uN) [TopologicalSpace N] [ChartedSpace H N] [IsManifold 𝓘(ℝ, H) ∞ N]
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure X) (a : X → ℂ), Measurable a → Integrable a μ →
    ∀ (j : C(X, N)) (h : M × N → E),
    ContMDiff (𝓘(ℝ, V).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞ h →
    (∀ p : M, Integrable (fun x => a x • h (p, j x)) μ) ∧
    ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ (fun p => ∫ x, a x • h (p, j x) ∂μ) ∧
    ∀ (p : M) (v : TangentSpace 𝓘(ℝ, V) p),
      mvfderiv 𝓘(ℝ, V) (fun q => ∫ x, a x • h (q, j x) ∂μ) p v =
        ∫ x, a x • mvfderiv 𝓘(ℝ, V) (fun q => h (q, j x)) p v ∂μ

/-- Absorb the magnitude into a finite measure and the phase into a compact coordinate,
then apply compact manifold integration with a continuous weight. -/
theorem compactManifoldIntegrableWeight :
    CompactManifoldIntegrableWeightStatement.{uX,uV,uM,uH,uN,uE} := by
  intro X _ _ _ _ V _ _ _ M _ _ _ H _ _ N _ _ _ E _ _ _ μ a ha hai j h hh
  let B := Metric.closedBall (0 : ℂ) 1
  let : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let θ (x : X) : ℂ := ‖a x‖⁻¹ • a x
  have hθ (x : X) : θ x ∈ B := by
    change θ x ∈ Metric.closedBall (0 : ℂ) 1
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖‖a x‖⁻¹ • a x‖ ≤ 1
    by_cases hx : a x = 0
    · simp [hx]
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  have hθa (x : X) : ‖a x‖ • θ x = a x := by
    by_cases hx : a x = 0
    · simp [θ, hx]
    · change ‖a x‖ • (‖a x‖⁻¹ • a x) = a x
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
  let θB (x : X) : B := ⟨θ x, hθ x⟩
  have hθB : Measurable θB := (ha.norm.inv.smul ha).subtype_mk
  let q (x : X) : X × B := (x, θB x)
  have hq : MeasurableEmbedding q := by
    refine ⟨fun _ _ e => congrArg Prod.fst e, measurable_id.prodMk hθB, ?_⟩
    intro s hs
    have he : q '' s =
        {z : X × B | z.2 = θB z.1} ∩ Prod.fst ⁻¹' s := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨rfl, hx⟩
      · rintro ⟨hz, hb⟩
        exact ⟨z.1, hb, Prod.ext rfl hz.symm⟩
    rw [he]
    exact (measurableSet_eq_fun measurable_snd (hθB.comp measurable_fst)).inter
      (measurable_fst hs)
  let δ (x : X) : ℝ≥0∞ := ‖a x‖ₑ
  let ν := μ.withDensity δ
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity
    (hasFiniteIntegral_iff_enorm.mp hai.hasFiniteIntegral).ne
  let τ := ν.map q
  let : IsFiniteMeasure τ := ν.isFiniteMeasure_map q
  let a' : C(X × B, ℂ) := ⟨fun z => z.2.val, continuous_subtype_val.comp continuous_snd⟩
  let j' : C(X × B, N) := ⟨fun z => j z.1, j.continuous.comp continuous_fst⟩
  have hintegral (k : X → E) : (∫ z, a' z • k z.1 ∂τ) = ∫ x, a x • k x ∂μ := by
    rw [hq.integral_map (μ := ν)]
    change (∫ x, θ x • k x ∂ν) = _
    rw [integral_withDensity_eq_integral_toReal_smul ha.enorm
      (Filter.Eventually.of_forall fun _ => enorm_lt_top)]
    apply integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change (‖a x‖ₑ).toReal • (θ x • k x) = a x • k x
    rw [toReal_enorm, ← smul_assoc, hθa]
  obtain ⟨_, hsmooth, _, hderiv⟩ := compactManifoldVectorIntegral
    (X × B) V M H N E τ a' j' h hh
  refine ⟨?_, ?_, ?_⟩
  · intro p
    have hc : Continuous (fun x => h (p, j x)) := hh.continuous.comp
      (continuous_const.prodMk j.continuous)
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
    exact hai.smul_bdd C hc.aestronglyMeasurable_of_compactSpace
      (Filter.Eventually.of_forall fun x => hC x (mem_univ x))
  · exact hsmooth.congr fun p => (hintegral (fun x => h (p, j x))).symm
  · intro p v
    have he : (fun p => ∫ z, a' z • h (p, j' z) ∂τ) =
        fun p => ∫ x, a x • h (p, j x) ∂μ :=
      funext fun p => hintegral (fun x => h (p, j x))
    rw [← he]
    exact (hderiv p v).trans (hintegral (fun x =>
      mvfderiv 𝓘(ℝ, V) (fun q => h (q, j x)) p v))

end Langlands.Analysis
