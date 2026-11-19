import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Weakly holomorphic operator families on a finite-dimensional complex space -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic.WeakHolomorphy

open Metric Set Filter Topology Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
  {C : Type*} [NormedAddCommGroup C] [NormedSpace ℂ C]

omit [NormedSpace ℂ E] in
/-- A weakly continuous family of operators out of a Banach space is uniformly bounded on a
compact set (uniform boundedness principle, applied twice). -/
theorem exists_bound_of_weak [CompleteSpace B] {g : E → B →L[ℂ] C} {K : Set E}
    (hK : IsCompact K) (hg : ∀ v (φ : StrongDual ℂ C), ContinuousOn (fun z => φ (g z v)) K) :
    ∃ M, ∀ z ∈ K, ‖g z‖ ≤ M := by
  have hpt : ∀ v, ∃ M, ∀ z : K, ‖g z v‖ ≤ M := by
    intro v
    obtain ⟨M, hM⟩ := banach_steinhaus
      (g := fun z : K => NormedSpace.inclusionInDoubleDual ℂ C (g z v)) (fun φ => by
        obtain ⟨c, hc⟩ := hK.exists_bound_of_continuousOn (hg v φ)
        exact ⟨c, fun z => by simpa using hc z z.2⟩)
    refine ⟨M, fun z => ?_⟩
    calc ‖g z v‖ = ‖NormedSpace.inclusionInDoubleDualLi ℂ (g z v)‖ :=
          ((NormedSpace.inclusionInDoubleDualLi (E := C) ℂ).norm_map (g z v)).symm
      _ ≤ M := hM z
  obtain ⟨M, hM⟩ := banach_steinhaus (g := fun z : K => g z) hpt
  exact ⟨M, fun z hz => hM ⟨z, hz⟩⟩

variable [FiniteDimensional ℂ E]

/-- A weakly holomorphic family of operators on an open subset of a finite-dimensional complex
space is Lipschitz in operator norm at each point (Banach–Steinhaus and the Schwarz lemma). -/
theorem exists_lipschitzAt_of_weak [CompleteSpace B] {g : E → B →L[ℂ] C} {T : Set E}
    (hT : IsOpen T) (hg : ∀ v (φ : StrongDual ℂ C), DifferentiableOn ℂ (fun z => φ (g z v)) T)
    {z₁ : E} (hz₁ : z₁ ∈ T) :
    ∃ r > 0, ∃ L, ∀ z ∈ ball z₁ r, ‖g z - g z₁‖ ≤ L * ‖z - z₁‖ := by
  obtain ⟨ε, hε, hεT⟩ := Metric.isOpen_iff.1 hT z₁ hz₁
  set R := ε / 2 with hR
  have hR0 : 0 < R := by positivity
  have hcl : closedBall z₁ R ⊆ T := (closedBall_subset_ball (by linarith)).trans hεT
  obtain ⟨M, hM⟩ := exists_bound_of_weak (isCompact_closedBall z₁ R)
    (fun v φ => ((hg v φ).mono hcl).continuousOn)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z₁ (mem_closedBall_self hR0.le))
  have hL0 : 0 ≤ 2 * M / R := div_nonneg (mul_nonneg zero_le_two hM0) hR0.le
  refine ⟨R, hR0, 2 * M / R, fun z hz => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hL0 (norm_nonneg _)) fun v => ?_
  refine NormedSpace.norm_le_dual_bound ℂ _
    (mul_nonneg (mul_nonneg hL0 (norm_nonneg _)) (norm_nonneg _)) fun φ => ?_
  set h : E → ℂ := fun w => φ (g w v) with hh
  have hd : DifferentiableOn ℂ h (ball z₁ R) := (hg v φ).mono (ball_subset_closedBall.trans hcl)
  have h1 : ∀ w ∈ closedBall z₁ R, ‖h w‖ ≤ M * ‖v‖ * ‖φ‖ := by
    intro w hw
    calc ‖h w‖ ≤ ‖φ‖ * ‖g w v‖ := φ.le_opNorm _
      _ ≤ ‖φ‖ * (‖g w‖ * ‖v‖) := by gcongr; exact (g w).le_opNorm v
      _ ≤ ‖φ‖ * (M * ‖v‖) := by gcongr; exact hM w hw
      _ = M * ‖v‖ * ‖φ‖ := by ring
  have hmaps : MapsTo h (ball z₁ R) (closedBall (h z₁) (2 * M * ‖v‖ * ‖φ‖)) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm]
    calc ‖h w - h z₁‖ ≤ ‖h w‖ + ‖h z₁‖ := norm_sub_le _ _
      _ ≤ M * ‖v‖ * ‖φ‖ + M * ‖v‖ * ‖φ‖ :=
          add_le_add (h1 w (ball_subset_closedBall hw)) (h1 z₁ (mem_closedBall_self hR0.le))
      _ = 2 * M * ‖v‖ * ‖φ‖ := by ring
  have hs := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps hz
  rw [dist_eq_norm, dist_eq_norm] at hs
  have heq : φ ((g z - g z₁) v) = h z - h z₁ := by simp [hh]
  rw [heq]
  calc ‖h z - h z₁‖ ≤ 2 * M * ‖v‖ * ‖φ‖ / R * ‖z - z₁‖ := hs
    _ = 2 * M / R * ‖z - z₁‖ * ‖v‖ * ‖φ‖ := by ring

/-- Big-`O` form of `exists_lipschitzAt_of_weak`: `g z - g z₁ = O(z - z₁)` as `z → z₁`. -/
theorem isBigO_sub_of_weak [CompleteSpace B] {g : E → B →L[ℂ] C} {T : Set E}
    (hT : IsOpen T) (hg : ∀ v (φ : StrongDual ℂ C), DifferentiableOn ℂ (fun z => φ (g z v)) T)
    {z₁ : E} (hz₁ : z₁ ∈ T) :
    (fun z => g z - g z₁) =O[𝓝 z₁] (fun z => z - z₁) := by
  obtain ⟨r, hr, L, hL⟩ := exists_lipschitzAt_of_weak hT hg hz₁
  refine IsBigO.of_bound L ?_
  filter_upwards [ball_mem_nhds z₁ hr] with z hz using hL z hz

/-- A weakly holomorphic family of operators is continuous in operator norm. -/
theorem continuousAt_of_weak [CompleteSpace B] {g : E → B →L[ℂ] C} {T : Set E}
    (hT : IsOpen T) (hg : ∀ v (φ : StrongDual ℂ C), DifferentiableOn ℂ (fun z => φ (g z v)) T)
    {z₁ : E} (hz₁ : z₁ ∈ T) : ContinuousAt g z₁ := by
  have h1 : Tendsto (fun z => z - z₁) (𝓝 z₁) (𝓝 0) :=
    tendsto_sub_nhds_zero_iff.2 tendsto_id
  exact tendsto_sub_nhds_zero_iff.1 ((isBigO_sub_of_weak hT hg hz₁).trans_tendsto h1)

/-- If `X` is a weakly holomorphic family of invertible operators on an open subset of a
finite-dimensional complex space, then so is the family of inverses `z ↦ (X z)⁻¹`. -/
theorem differentiableOn_inverse_apply [CompleteSpace B] {X : E → B →L[ℂ] B} {T : Set E}
    (hT : IsOpen T) (hX : ∀ v (φ : StrongDual ℂ B), DifferentiableOn ℂ (fun z => φ (X z v)) T)
    (hunit : ∀ z ∈ T, IsUnit (X z)) (w : B) (φ : StrongDual ℂ B) :
    DifferentiableOn ℂ (fun z => φ (Ring.inverse (X z) w)) T := by
  intro z₁ hz₁
  refine DifferentiableAt.differentiableWithinAt ?_
  have hn : T ∈ 𝓝 z₁ := hT.mem_nhds hz₁
  have e1 : ∀ z ∈ T, X z (Ring.inverse (X z) w) = w := by
    intro z hz
    obtain ⟨u, hu⟩ := hunit z hz
    rw [← hu, Ring.inverse_unit, ← mul_apply_eq_comp, Units.mul_inv,
      one_apply_eq_self]
  have e2 : ∀ t, Ring.inverse (X z₁) (X z₁ t) = t := by
    intro t
    obtain ⟨u, hu⟩ := hunit z₁ hz₁
    rw [← hu, Ring.inverse_unit, ← mul_apply_eq_comp, Units.inv_mul,
      one_apply_eq_self]
  set ψ : StrongDual ℂ B := φ ∘L Ring.inverse (X z₁) with hψ
  set y₁ : B := Ring.inverse (X z₁) w with hy₁
  have had : HasFDerivAt (fun z => ψ (X z y₁)) (fderiv ℂ (fun z => ψ (X z y₁)) z₁) z₁ :=
    ((hX y₁ ψ) z₁ hz₁).differentiableAt hn |>.hasFDerivAt
  have hYc : ContinuousAt (fun z => Ring.inverse (X z)) z₁ := by
    obtain ⟨u, hu⟩ := hunit z₁ hz₁
    have h := NormedRing.inverse_continuousAt u
    rw [hu] at h
    exact h.comp (continuousAt_of_weak hT hX hz₁)
  have hyc : ContinuousAt (fun z => Ring.inverse (X z) w) z₁ := hYc.clm_apply continuousAt_const
  set r : E → ℂ := fun z => ψ ((X z - X z₁) (Ring.inverse (X z) w - y₁)) with hr
  have hro : r =o[𝓝 z₁] (fun z => z - z₁) := by
    have h1 : (fun z => ‖X z - X z₁‖ * ‖Ring.inverse (X z) w - y₁‖) =o[𝓝 z₁]
        (fun z => ‖z - z₁‖ * 1) := by
      refine (isBigO_sub_of_weak hT hX hz₁).norm_norm.mul_isLittleO ?_
      refine IsLittleO.norm_left ((isLittleO_one_iff ℝ).2 ?_)
      exact tendsto_sub_nhds_zero_iff.2 hyc
    have h2 : r =O[𝓝 z₁] (fun z => ‖X z - X z₁‖ * ‖Ring.inverse (X z) w - y₁‖) := by
      refine IsBigO.of_bound ‖ψ‖ (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact (ψ.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left ((X z - X z₁).le_opNorm _) (norm_nonneg _))
    refine (h2.trans_isLittleO h1).trans_isBigO ?_
    simp only [mul_one]
    exact (isBigO_refl _ _).norm_left
  have hrd : HasFDerivAt r (0 : E →L[ℂ] ℂ) z₁ := by
    rw [hasFDerivAt_iff_isLittleO]
    have h0 : r z₁ = 0 := by simp [hr]
    simpa [h0] using hro
  have hid : (fun z => φ (Ring.inverse (X z) w)) =ᶠ[𝓝 z₁]
      (fun z => φ y₁ - (ψ (X z y₁) - ψ (X z₁ y₁)) - r z) := by
    filter_upwards [hn] with z hz
    simp only [hr, hψ, hy₁, ContinuousLinearMap.comp_apply, map_sub,
      sub_apply, e1 z hz, e2]
    ring
  exact (((hasFDerivAt_const (φ y₁) z₁).sub (had.sub_const _)).sub hrd).congr_of_eventuallyEq
    hid |>.differentiableAt

end Langlands.Analysis.Meromorphic.WeakHolomorphy
