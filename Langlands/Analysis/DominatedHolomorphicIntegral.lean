import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # A locally dominated integral of holomorphic functions -/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology

set_option autoImplicit false

namespace Langlands.Analysis

variable {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace α]

private theorem norm_fderiv_le_of_bound_on_ball {f : E → ℂ} {c x : E} {R C : ℝ}
    (hR : 0 < R) (hx : x ∈ ball c R) (hf : DifferentiableOn ℂ f (ball c (2 * R)))
    (hC : ∀ y ∈ ball c (2 * R), ‖f y‖ ≤ C) : ‖fderiv ℂ f x‖ ≤ C / R := by
  have hx' : x ∈ ball c (2 * R) := ball_subset_ball (by linarith) hx
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans (hC x hx')
  have hfx := hf.differentiableAt (isOpen_ball.mem_nhds hx')
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hC₀ hR.le)
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hv₀ : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let ρ := R / ‖v‖
  have hρ : 0 < ρ := div_pos hR hv₀
  let g : ℂ → ℂ := fun z => f (x + z • v)
  have hm : MapsTo (fun z : ℂ => x + z • v) (closedBall 0 ρ) (ball c (2 * R)) := by
    intro z hz
    have hz' : ‖z‖ ≤ ρ := by simpa only [mem_closedBall_zero_iff] using hz
    have hzv : ‖z • v‖ ≤ R := by
      rw [norm_smul]
      exact (le_div_iff₀ hv₀).1 hz'
    have hxle : ‖x - c‖ < R := by simpa only [mem_ball, dist_eq_norm] using hx
    rw [mem_ball, dist_eq_norm, show x + z • v - c = (x - c) + z • v by abel]
    exact (norm_add_le _ _).trans_lt (by linarith)
  have hgd : DifferentiableOn ℂ g (closedBall 0 ρ) := hf.comp
    ((differentiable_id.smul_const v).const_add x).differentiableOn hm
  have hgv : HasDerivAt (fun z : ℂ => x + z • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
  have hgg : HasDerivAt g (fderiv ℂ f x v) 0 := by
    have hh : HasFDerivAt f (fderiv ℂ f x) (x + (0 : ℂ) • v) := by simpa using hfx.hasFDerivAt
    exact hh.comp_hasDerivAt _ hgv
  rw [← hgg.deriv]
  refine (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ
    (hgd.mono closure_ball_subset_closedBall).diffContOnCl (fun z hz =>
      hC _ (hm (sphere_subset_closedBall hz)))).trans_eq ?_
  dsimp [ρ]
  field_simp

private theorem aeStronglyMeasurable_fderiv_apply {μ : Measure α} {F : E → α → ℂ} {x : E}
    (hF : ∀ z, AEStronglyMeasurable (F z) μ)
    (hD : ∀ᵐ a ∂μ, DifferentiableAt ℂ (F · a) x) (v : E) :
    AEStronglyMeasurable (fun a => fderiv ℂ (F · a) x v) μ := by
  let S (z : ℂ) (a : α) : ℂ := slope (fun t : ℂ => F (x + t • v) a) 0 z
  apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℂ)) (f := S)
  · intro z
    have hS : S z = z⁻¹ • (F (x + z • v) - F x) := by
      funext a
      simp [S, slope]
    rw [hS]
    exact ((hF (x + z • v)).sub (hF x)).const_smul z⁻¹
  · filter_upwards [hD] with a ha
    have hv : HasDerivAt (fun t : ℂ => x + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
    have hh : HasFDerivAt (F · a) (fderiv ℂ (F · a) x) (x + (0 : ℂ) • v) := by
      simpa using ha.hasFDerivAt
    have h := (hh.comp_hasDerivAt 0 hv).tendsto_slope_zero
    simpa [S, Function.comp_def, slope, smul_eq_mul] using h

private theorem aeStronglyMeasurable_fderiv [FiniteDimensional ℂ E]
    {μ : Measure α} {F : E → α → ℂ} {x : E}
    (hF : ∀ z, AEStronglyMeasurable (F z) μ)
    (hD : ∀ᵐ a ∂μ, DifferentiableAt ℂ (F · a) x) :
    AEStronglyMeasurable (fun a => fderiv ℂ (F · a) x) μ := by
  let b := Module.Free.chooseBasis ℂ E
  let ℓ i := (b.coord i).toContinuousLinearMap
  have h : (fun a => fderiv ℂ (F · a) x) = fun a => ∑ i, fderiv ℂ (F · a) x (b i) • ℓ i := by
    funext a
    ext v
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul, sum_apply, smul_apply,
      ℓ, LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact mul_comm _ _
  have hsum : (fun a => ∑ i, fderiv ℂ (F · a) x (b i) • ℓ i) =
      ∑ i, (fun a => fderiv ℂ (F · a) x (b i)) • (fun _ : α => ℓ i) := by
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply']
  rw [h, hsum]
  exact Finset.aestronglyMeasurable_sum _ fun i _ =>
    (aeStronglyMeasurable_fderiv_apply hF hD (b i)).smul
      (aestronglyMeasurable_const (b := ℓ i))

/-- A locally integrably dominated family of scalar holomorphic functions on a finite-dimensional
complex parameter space can be integrated without losing holomorphy. -/
def DominatedHolomorphicIntegralStatement (E α : Type*)
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [MeasurableSpace α] : Prop :=
  ∀ (μ : Measure α) (S : Set E) (F : E → α → ℂ),
    (∀ p, AEStronglyMeasurable (F p) μ) →
    (∀ᵐ a ∂μ, DifferentiableOn ℂ (F · a) S) →
    (∀ p ∈ S, ∃ R : ℝ, 0 < R ∧ ball p (2 * R) ⊆ S ∧
      ∃ B : α → ℝ, Integrable B μ ∧ ∀ᵐ a ∂μ, ∀ q ∈ ball p (2 * R), ‖F q a‖ ≤ B a) →
    (∀ p ∈ S, Integrable (F p) μ) ∧ DifferentiableOn ℂ (fun p => ∫ a, F p a ∂μ) S

/-- Cauchy's estimate supplies the local bound required to differentiate under the integral. -/
theorem dominatedHolomorphicIntegral [FiniteDimensional ℂ E] : DominatedHolomorphicIntegralStatement E α := by
  intro μ S F hM hD hB
  have hi (p : E) (hp : p ∈ S) : Integrable (F p) μ := by
    obtain ⟨R, hR, _, B, hBi, hBd⟩ := hB p hp
    exact hBi.mono' (hM p) (hBd.mono fun a ha => ha p (mem_ball_self (by positivity)))
  refine ⟨hi, fun p hp => ?_⟩
  obtain ⟨R, hR, hRS, B, hBi, hBd⟩ := hB p hp
  have hsub : ball p R ⊆ ball p (2 * R) := ball_subset_ball (by linarith)
  have hDiff : ∀ᵐ a ∂μ, ∀ q ∈ ball p (2 * R), DifferentiableAt ℂ (F · a) q :=
    hD.mono fun a ha q hq => (ha.mono hRS).differentiableAt (isOpen_ball.mem_nhds hq)
  have hMeas := aeStronglyMeasurable_fderiv hM
    (hDiff.mono fun a ha => ha p (mem_ball_self (by positivity)))
  refine (hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := fun q a => fderiv ℂ (F · a) q)
    (ball_mem_nhds p hR)
    (Eventually.of_forall hM) (hi p hp) hMeas ?_ (hBi.div_const R) ?_).differentiableAt.differentiableWithinAt
  · filter_upwards [hD, hBd] with a ha hab q hq
    exact norm_fderiv_le_of_bound_on_ball hR hq (ha.mono hRS) hab
  · exact hDiff.mono fun a ha q hq => (ha q (hsub hq)).hasFDerivAt

end Langlands.Analysis
