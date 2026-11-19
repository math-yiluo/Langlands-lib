import Langlands.Representation.Archimedean.HilbertContragredient
import Langlands.Representation.Archimedean.RightKernelOperatorContinuity
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Joint continuity of the inverse-adjoint Hilbert action -/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped InnerProduct InnerProductSpace Pointwise Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

section ContinuousOrbits

variable {G : Type*} [Group G] [TopologicalSpace G]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] (S : G →* (H →L[ℂ] H))

/-- Vectors whose orbit under the supplied action is norm continuous at the identity. -/
def continuousOrbitVectors : Submodule ℂ H where
  carrier := {v | ContinuousAt (fun g => S g v) 1}
  zero_mem' := by
    change ContinuousAt (fun g => S g 0) 1
    simp only [map_zero]
    exact continuousAt_const
  add_mem' {v w} hv hw := by
    change ContinuousAt (fun g => S g v) 1 at hv
    change ContinuousAt (fun g => S g w) 1 at hw
    change ContinuousAt (fun g => S g (v + w)) 1
    simp only [map_add]
    exact hv.add hw
  smul_mem' c v hv := by
    change ContinuousAt (fun g => S g v) 1 at hv
    change ContinuousAt (fun g => S g (c • v)) 1
    simp only [map_smul]
    exact hv.const_smul c

private theorem isClosed_continuousOrbitVectors {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᶠ g in 𝓝 (1 : G), ‖S g‖ ≤ B) :
    IsClosed (continuousOrbitVectors S : Set H) := by
  apply isClosed_of_closure_subset
  intro v hv
  change ContinuousAt (fun g => S g v) 1
  change Tendsto (fun g => S g v) (𝓝 1) (𝓝 (S 1 v))
  rw [map_one, one_apply_eq_self]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := (ε / 2) / (B + 1)
  have hBp : 0 < B + 1 := by positivity
  obtain ⟨w, hw, hvw⟩ := Metric.mem_closure_iff.mp hv δ (div_pos (half_pos hε) hBp)
  have hw' : Tendsto (fun g => S g w) (𝓝 1) (𝓝 w) := by
    change ContinuousAt (fun g => S g w) 1 at hw
    simpa only [ContinuousAt, map_one, one_apply_eq_self] using hw
  have hn := Metric.tendsto_nhds.mp hw' (ε / 2) (half_pos hε)
  have hδ : (B + 1) * dist v w < ε / 2 := by
    rw [mul_comm (B + 1)]
    exact (lt_div_iff₀ hBp).mp hvw
  filter_upwards [hbound, hn] with g hg hgw
  have hdist : dist (S g v) (S g w) ≤ B * dist v w := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact ((S g).le_opNorm _).trans (mul_le_mul_of_nonneg_right hg (norm_nonneg _))
  calc
    _ ≤ dist (S g v) (S g w) + (dist (S g w) w + dist w v) := by
      simpa only [add_assoc] using dist_triangle4 (S g v) (S g w) w v
    _ ≤ B * dist v w + (dist (S g w) w + dist w v) := add_le_add hdist le_rfl
    _ = (B + 1) * dist v w + dist (S g w) w := by rw [dist_comm w v]; ring
    _ < ε := by linarith

variable [IsTopologicalGroup G]

private theorem continuous_orbit_of_mem_continuousOrbitVectors {v : H}
    (hv : v ∈ continuousOrbitVectors S) : Continuous (fun g => S g v) := by
  apply continuous_iff_continuousAt.mpr
  intro g
  have h : ContinuousAt (fun a => S a v) (g⁻¹ * g) := by
    rw [inv_mul_cancel]
    exact hv
  have hc : ContinuousAt (fun a : G => g⁻¹ * a) g :=
    (continuous_const.mul continuous_id).continuousAt
  have h' : ContinuousAt (fun a => S g (S (g⁻¹ * a) v)) g :=
    (S g).continuous.continuousAt.comp (h.comp hc)
  have he (a : G) : S g (S (g⁻¹ * a) v) = S a v := by
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left]
  simp_rw [he] at h'
  exact h'

omit [IsTopologicalGroup G] in
private theorem isContinuousRepresentation_of_orbits
    (horbit : ∀ v : H, Continuous (fun g => S g v))
    (hbound : ∀ g : G, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ h in 𝓝 g, ‖S h‖ ≤ B) :
    IsContinuousRepresentation S := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨g, v⟩
  obtain ⟨B, hB, hg⟩ := hbound g
  change Tendsto (fun p : G × H => S p.1 p.2) (𝓝 (g, v)) (𝓝 (S g v))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h : Tendsto (fun p : G × H => B * ‖p.2 - v‖ + ‖S p.1 v - S g v‖)
      (𝓝 (g, v)) (𝓝 0) := by
    have hc : Continuous (fun p : G × H => B * ‖p.2 - v‖ + ‖S p.1 v - S g v‖) :=
      (continuous_const.mul (continuous_snd.sub continuous_const).norm).add
        (((horbit v).comp continuous_fst).sub continuous_const).norm
    simpa only [sub_self, norm_zero, mul_zero, add_zero] using hc.tendsto (g, v)
  refine squeeze_zero' (Eventually.of_forall fun p => norm_nonneg _) ?_ h
  filter_upwards [continuous_fst.continuousAt hg] with p hp
  change ‖S p.1‖ ≤ B at hp
  calc
    _ = ‖S p.1 (p.2 - v) + (S p.1 v - S g v)‖ := by rw [map_sub]; congr 1; abel
    _ ≤ ‖S p.1 (p.2 - v)‖ + ‖S p.1 v - S g v‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (((S p.1).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hp (norm_nonneg _))) le_rfl

end ContinuousOrbits

section Hilbert

open DerivativeSmoothVectors

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (R : Aˣ →* (H →L[ℂ] H))

local notation "𝓜" => 𝓘(ℝ, A)

section Measure

variable [MeasurableSpace Aˣ] [BorelSpace Aˣ] (μ : Measure Aˣ)
  [IsFiniteMeasureOnCompacts μ] [μ.IsMulRightInvariant] [μ.IsOpenPosMeasure]

omit [μ.IsMulRightInvariant] in
private theorem exists_smoothedOperator_apply_ne_zero (hR : IsContinuousRepresentation R)
    {v : H} (hv : v ≠ 0) :
    ∃ (κ : Aˣ → ℂ) (hκ : Continuous κ) (hc : HasCompactSupport κ),
      smoothedOperator R μ hR κ hκ hc v ≠ 0 := by
  let L : H →L[ℝ] ℝ := Complex.reCLM.comp ((innerSL ℂ v).restrictScalars ℝ)
  let q := fun g : Aˣ => L (R g v)
  have hq : Continuous q := L.continuous.comp (hR.comp (continuous_id.prodMk continuous_const))
  have hqone : 0 < q 1 := by
    change 0 < RCLike.re (inner ℂ v (R 1 v))
    rw [map_one, one_apply_eq_self, ← norm_sq_eq_re_inner]
    positivity
  let U : Set Aˣ := {g | 0 < q g⁻¹}
  have hU : U ∈ 𝓝 (1 : Aˣ) := by
    have hqi : Continuous (fun g : Aˣ => q g⁻¹) := hq.comp continuous_inv
    exact hqi.continuousAt (lt_mem_nhds (by simpa only [inv_one] using hqone))
  obtain ⟨b, hb, hbcs, hbU, hb0, hb1, -, -⟩ :=
    Langlands.Analysis.smoothNormalizedInverseKernel A Aˣ μ U hU
  let κ : Aˣ → ℂ := fun g => b g
  have hκ : Continuous κ := Complex.continuous_ofReal.comp hb.continuous
  have hc : HasCompactSupport κ := hbcs.comp_left Complex.ofReal_zero
  refine ⟨κ, hκ, hc, fun he => ?_⟩
  let a := fun g : Aˣ => b g⁻¹ * q g
  have hac : Continuous a := (hb.continuous.comp continuous_inv).mul hq
  have hbc : HasCompactSupport (fun g => b g⁻¹) := hbcs.comp_homeomorph (Homeomorph.inv Aˣ)
  have has : HasCompactSupport a := hbc.mul_right
  have ha0 (g : Aˣ) : 0 ≤ a g := by
    by_cases hz : b g⁻¹ = 0
    · simp [a, hz]
    · have h := hbU (subset_tsupport b hz)
      have hg : 0 < q g := by simpa [U] using h
      exact mul_nonneg (hb0 _) hg.le
  have ha1 : a 1 ≠ 0 := (by simpa [a] using mul_pos hb1 hqone : 0 < a 1).ne'
  have hI : 0 < ∫ g, a g ∂μ := hac.integral_pos_of_hasCompactSupport_nonneg_nonzero has ha0 ha1
  have hi : Integrable (fun g : Aˣ => κ g⁻¹ • R g v) μ := by
    have hOrbit : Continuous (fun g : Aˣ => R g v) :=
      hR.comp (continuous_id.prodMk continuous_const)
    exact ((hκ.comp continuous_inv).smul hOrbit).integrable_of_hasCompactSupport
      ((hc.comp_homeomorph (Homeomorph.inv Aˣ)).smul_right)
  have hval : L (smoothedOperator R μ hR κ hκ hc v) = ∫ g, a g ∂μ := by
    rw [smoothedOperator_apply, smoothedVector, ← L.integral_comp_comm hi]
    apply integral_congr_ae
    filter_upwards with g
    rw [show κ g⁻¹ • R g v = b g⁻¹ • R g v from algebraMap_smul ℂ (b g⁻¹) (R g v), map_smul]
    rfl
  rw [he, map_zero] at hval
  exact hI.ne' hval.symm

omit [μ.IsOpenPosMeasure] in
private theorem adjoint_smoothing_mem_continuousOrbitVectors (hR : IsContinuousRepresentation R)
    (κ : Aˣ → ℂ) (hκ : Continuous κ) (hc : HasCompactSupport κ) (v : H) :
    ((smoothedOperator R μ hR κ hκ hc)†) v ∈ continuousOrbitVectors (hilbertContragredient R) := by
  let T := smoothedOperator R μ hR κ hκ hc
  have han := continuousAt_smoothedOperator_comp_inv R μ hR κ hκ hc
  have ha : ContinuousAt (fun g => (T.comp (R g⁻¹))†) (1 : Aˣ) :=
    ContinuousLinearMap.adjoint.continuous.continuousAt.comp han
  have he : ContinuousAt (fun g => ((T.comp (R g⁻¹))†) v) (1 : Aˣ) :=
    (ContinuousLinearMap.apply ℂ H v).continuous.continuousAt.comp ha
  change ContinuousAt (fun g : Aˣ => hilbertContragredient R g ((T†) v)) 1
  simpa only [Function.comp_apply, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_apply, hilbertContragredient_apply] using he

include μ in
private theorem continuousOrbitVectors_hilbertContragredient_eq_top
    (hR : IsContinuousRepresentation R) : continuousOrbitVectors (hilbertContragredient R) = ⊤ := by
  let : LocallyCompactSpace Aˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  let V := continuousOrbitVectors (hilbertContragredient R)
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (1 : Aˣ)
  obtain ⟨B, hB, hBd⟩ := hR.exists_opNorm_le_of_isCompact hK.inv
  have hnear : ∀ᶠ g in 𝓝 (1 : Aˣ), ‖hilbertContragredient R g‖ ≤ B := by
    filter_upwards [hKn] with g hg
    rw [norm_hilbertContragredient]
    exact hBd _ (by simpa)
  have hc : IsClosed (V : Set H) := isClosed_continuousOrbitVectors _ hB hnear
  have hv : Vᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro v hv
    apply (Submodule.mem_bot ℂ).mpr
    by_contra hne
    obtain ⟨κ, hκ, hk, hTv⟩ := exists_smoothedOperator_apply_ne_zero R μ hR hne
    let T := smoothedOperator R μ hR κ hκ hk
    have hw : (T†) (T v) ∈ V := adjoint_smoothing_mem_continuousOrbitVectors R μ hR κ hκ hk (T v)
    have hinner := (V.mem_orthogonal _).mp hv _ hw
    rw [ContinuousLinearMap.adjoint_inner_left] at hinner
    exact hTv (inner_self_eq_zero.mp hinner)
  change V = ⊤
  rw [← hc.submodule_topologicalClosure_eq, ← V.orthogonal_orthogonal_eq_closure, hv,
    Submodule.bot_orthogonal_eq_top]

end Measure

/-- A jointly continuous Hilbert representation of the actual units group has a jointly
continuous inverse-adjoint action. -/
theorem isContinuousRepresentation_hilbertContragredient (hR : IsContinuousRepresentation R) :
    IsContinuousRepresentation (hilbertContragredient R) := by
  let : MeasurableSpace Aˣ := borel Aˣ
  let : BorelSpace Aˣ := ⟨rfl⟩
  let : LocallyCompactSpace Aˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  let μ := (Measure.haar : Measure Aˣ).inv
  have hV := continuousOrbitVectors_hilbertContragredient_eq_top R μ hR
  apply isContinuousRepresentation_of_orbits
  · intro v
    apply continuous_orbit_of_mem_continuousOrbitVectors
    rw [hV]
    exact Submodule.mem_top
  · intro g
    obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds g
    obtain ⟨B, hB, hBd⟩ := hR.exists_opNorm_le_of_isCompact hK.inv
    refine ⟨B, hB, ?_⟩
    filter_upwards [hKn] with h hh
    rw [norm_hilbertContragredient]
    exact hBd _ (by simpa)

end Hilbert
end Langlands.Archimedean
