import Langlands.Representation.Archimedean.SmoothDualEvaluation

/-! # The norm-continuous part of a Banach contragredient -/

noncomputable section

open Filter Set MeasureTheory
open scoped Topology Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.NormContinuousDual

section Action

variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup E] [NormedSpace ℂ E] (R : G →* (E →L[ℂ] E))

/-- Bounded functionals whose orbit is continuous in the operator norm at the identity. -/
abbrev space : Submodule ℂ (StrongDual ℂ E) :=
  continuousOrbitVectors (continuousDualRepresentation R)

private theorem orbitContinuous (L : space R) :
    Continuous (fun g => continuousDualRepresentation R g L.val) := by
  let S := continuousDualRepresentation R
  apply continuous_iff_continuousAt.mpr
  intro g
  have hL : ContinuousAt (fun a => S a L.val) 1 := L.property
  have hL' : ContinuousAt (fun a => S a L.val) (g⁻¹ * g) := by
    simpa only [inv_mul_cancel] using hL
  have ht : ContinuousAt (fun a : G => g⁻¹ * a) g :=
    (continuous_const.mul continuous_id).continuousAt
  have h := (S g).continuous.continuousAt.comp (hL'.comp ht)
  have he (a : G) : S g (S (g⁻¹ * a) L.val) = S a L.val := by
    calc
      _ = S (g * (g⁻¹ * a)) L.val := by rw [S.map_mul g (g⁻¹ * a)]; rfl
      _ = _ := by rw [mul_inv_cancel_left]
  change ContinuousAt (fun a => S g (S (g⁻¹ * a) L.val)) g at h
  simpa only [he] using h

/-- The inverse-precomposition action preserves the norm-continuous part. -/
theorem action_mem (g : G) (L : space R) :
    continuousDualRepresentation R g L.val ∈ space R := by
  let S := continuousDualRepresentation R
  change ContinuousAt (fun h => S h (S g L.val)) 1
  have he (h : G) : S h (S g L.val) = S (h * g) L.val := by rw [S.map_mul h g]; rfl
  have hc : Continuous (fun h : G => S (h * g) L.val) :=
    (orbitContinuous R L).comp (continuous_id.mul continuous_const)
  simpa only [he] using hc.continuousAt (x := (1 : G))

/-- The Banach contragredient action restricted to its norm-continuous part. -/
def representation : G →* (space R →L[ℂ] space R) where
  toFun g := (continuousDualRepresentation R g).restrict (fun L hL => action_mem R g ⟨L, hL⟩)
  map_one' := by
    apply ContinuousLinearMap.ext
    intro L
    apply Subtype.ext
    change continuousDualRepresentation R 1 L.val = L.val
    rw [(continuousDualRepresentation R).map_one]
    rfl
  map_mul' g h := by
    apply ContinuousLinearMap.ext
    intro L
    apply Subtype.ext
    change continuousDualRepresentation R (g * h) L.val =
      continuousDualRepresentation R g (continuousDualRepresentation R h L.val)
    rw [(continuousDualRepresentation R).map_mul]
    rfl

@[simp]
theorem representation_apply (g : G) (L : space R) (v : E) :
    (representation R g L).val v = L.val (R g⁻¹ v) := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem norm_action_le (g : G) : ‖continuousDualRepresentation R g‖ ≤ ‖R g⁻¹‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro L
  change ‖L.comp (R g⁻¹)‖ ≤ ‖R g⁻¹‖ * ‖L‖
  exact (L.opNorm_comp_le _).trans_eq (mul_comm _ _)

variable [CompleteSpace E] [LocallyCompactSpace G]

private theorem localBound (hR : IsContinuousRepresentation R) (g : G) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ h in 𝓝 g, ‖continuousDualRepresentation R h‖ ≤ B := by
  obtain ⟨K, hK, hKg⟩ := exists_compact_mem_nhds g
  obtain ⟨B, hB, hg⟩ := hR.exists_opNorm_le_of_isCompact hK.inv
  have hk : ∀ᶠ h in 𝓝 g, h ∈ K := hKg
  exact ⟨B, hB, hk.mono fun h hh => (norm_action_le R h).trans (hg _ (by simpa))⟩

/-- The norm-continuous part is a closed subspace of the normed dual. -/
theorem isClosed_space (hR : IsContinuousRepresentation R) :
    IsClosed (space R : Set (StrongDual ℂ E)) := by
  let S := continuousDualRepresentation R
  obtain ⟨B, hB, hn⟩ := localBound R hR 1
  apply isClosed_of_closure_subset
  intro L hL
  change Tendsto (fun g => S g L) (𝓝 1) (𝓝 (S 1 L))
  rw [map_one, one_apply_eq_self]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hB₁ : 0 < B + 1 := by positivity
  obtain ⟨M, hM, hLM⟩ := Metric.mem_closure_iff.mp hL _ (div_pos (half_pos hε) hB₁)
  have hM₁ : Tendsto (fun g => S g M) (𝓝 1) (𝓝 M) := by
    change Tendsto (fun g => S g M) (𝓝 1) (𝓝 (S 1 M)) at hM
    rwa [map_one, one_apply_eq_self] at hM
  have hδ := (lt_div_iff₀ hB₁).mp hLM
  filter_upwards [hn, Metric.tendsto_nhds.mp hM₁ _ (half_pos hε)] with g hg hgM
  have hdist : dist (S g L) (S g M) ≤ B * dist L M := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact (S g).le_of_opNorm_le hg _
  calc
    dist (S g L) L ≤ dist (S g L) (S g M) + (dist (S g M) M + dist M L) := by
      simpa only [add_assoc] using dist_triangle4 (S g L) (S g M) M L
    _ ≤ B * dist L M + (dist (S g M) M + dist M L) := add_le_add hdist le_rfl
    _ = dist L M * (B + 1) + dist (S g M) M := by rw [dist_comm M L]; ring
    _ < ε := by linarith

/-- With the operator norm, the restricted contragredient is a Banach space. -/
theorem completeSpace (hR : IsContinuousRepresentation R) : CompleteSpace (space R) :=
  (isClosed_space R hR).completeSpace_coe

/-- The restricted contragredient action is jointly norm continuous. -/
theorem isContinuousRepresentation (hR : IsContinuousRepresentation R) :
    IsContinuousRepresentation (representation R) := by
  let S := continuousDualRepresentation R
  change Continuous (fun p : G × space R => ⟨S p.1 p.2.val, action_mem R p.1 p.2⟩ : _ → space R)
  apply Continuous.subtype_mk
  apply continuous_iff_continuousAt.mpr
  rintro ⟨g, L⟩
  obtain ⟨B, hB, hg⟩ := localBound R hR g
  change Tendsto (fun p : G × space R => S p.1 p.2.val) (𝓝 (g, L)) (𝓝 (S g L.val))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hε : Tendsto (fun p : G × space R =>
      B * ‖p.2.val - L.val‖ + ‖S p.1 L.val - S g L.val‖) (𝓝 (g, L)) (𝓝 0) := by
    have h : Continuous (fun p : G × space R =>
        B * ‖p.2.val - L.val‖ + ‖S p.1 L.val - S g L.val‖) :=
      (continuous_const.mul ((continuous_subtype_val.comp continuous_snd).sub
        continuous_const).norm).add
        (((orbitContinuous R L).comp continuous_fst).sub continuous_const).norm
    simpa only [sub_self, norm_zero, mul_zero, add_zero] using h.tendsto (g, L)
  refine squeeze_zero' (Eventually.of_forall fun p => norm_nonneg _) ?_ hε
  filter_upwards [continuous_fst.continuousAt hg] with p hp
  change ‖S p.1‖ ≤ B at hp
  calc
    ‖S p.1 p.2.val - S g L.val‖ = ‖S p.1 (p.2.val - L.val) + (S p.1 L.val - S g L.val)‖ := by
      rw [map_sub]
      congr 1
      abel
    _ ≤ ‖S p.1 (p.2.val - L.val)‖ + ‖S p.1 L.val - S g L.val‖ := norm_add_le _ _
    _ ≤ _ := add_le_add ((S p.1).le_of_opNorm_le hp _) le_rfl

end Action

section Units

open DerivativeSmoothVectors

variable {A E : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (R : Aˣ →* (E →L[ℂ] E))

private theorem smoothed_mem_space [MeasurableSpace Aˣ] [BorelSpace Aˣ]
    (μ : Measure Aˣ) [IsFiniteMeasureOnCompacts μ] [μ.IsMulRightInvariant]
    (hR : IsContinuousRepresentation R)
    (κ : Aˣ → ℂ) (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    (L : StrongDual ℂ E) :
    L.comp (smoothedOperator R μ hR κ hκ hκc) ∈ space R := by
  let T := smoothedOperator R μ hR κ hκ hκc
  have h := continuousAt_smoothedOperator_comp_inv R μ hR κ hκ hκc
  have hc := (L.postcomp (σ := RingHom.id ℂ) E).continuous.continuousAt.comp h
  change ContinuousAt (fun g : Aˣ => L.comp (T.comp (R g⁻¹))) 1 at hc
  exact hc

/-- On the units of a finite-dimensional real Banach algebra, the norm-continuous dual
separates points of the original Banach space. -/
theorem separates (hR : IsContinuousRepresentation R) {v : E} (hv : v ≠ 0) :
    ∃ L : space R, L.val v ≠ 0 := by
  let : LocallyCompactSpace Aˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  let : MeasurableSpace Aˣ := borel Aˣ
  let : BorelSpace Aˣ := ⟨rfl⟩
  let μ := (Measure.haar : Measure Aˣ).inv
  obtain ⟨L, -, hLv⟩ := exists_dual_vector ℂ v (norm_ne_zero_iff.mpr hv)
  let q (g : Aˣ) := (L (R g v)).re
  have hq : Continuous q := Complex.continuous_re.comp
    (L.continuous.comp (hR.comp (continuous_id.prodMk continuous_const)))
  have hq₁ : 0 < q 1 := by
    change 0 < (L (R 1 v)).re
    rw [map_one, one_apply_eq_self, hLv]
    exact norm_pos_iff.mpr hv
  let U := {g : Aˣ | 0 < q g⁻¹}
  have hU : U ∈ 𝓝 (1 : Aˣ) := by
    have hqc : Continuous (fun g : Aˣ => q g⁻¹) := hq.comp continuous_inv
    exact hqc.continuousAt (lt_mem_nhds (by simpa only [inv_one] using hq₁))
  obtain ⟨b, hb, hbc, hbU, hb₀, hb₁, -, -⟩ :=
    Langlands.Analysis.smoothNormalizedInverseKernel A Aˣ μ U hU
  let κ : Aˣ → ℂ := fun g => b g
  have hκ : Continuous κ := Complex.continuous_ofReal.comp hb.continuous
  have hκc : HasCompactSupport κ := hbc.comp_left Complex.ofReal_zero
  let T := smoothedOperator R μ hR κ hκ hκc
  refine ⟨⟨L.comp T, smoothed_mem_space R μ hR κ hκ hκc L⟩, fun hzero => ?_⟩
  let a (g : Aˣ) := b g⁻¹ * q g
  have ha : Continuous a := (hb.continuous.comp continuous_inv).mul hq
  have ha₀ (g : Aˣ) : 0 ≤ a g := by
    by_cases hg : b g⁻¹ = 0
    · simp [a, hg]
    · have h : 0 < q (g⁻¹)⁻¹ := hbU (subset_tsupport b hg)
      rw [inv_inv] at h
      exact mul_nonneg (hb₀ _) h.le
  have ha₁ : 0 < a 1 := mul_pos (by simpa only [inv_one] using hb₁) hq₁
  have hac : HasCompactSupport a := (hbc.comp_homeomorph (Homeomorph.inv Aˣ)).mul_right
  have hpos : 0 < ∫ g, a g ∂μ := ha.integral_pos_of_hasCompactSupport_nonneg_nonzero hac ha₀ ha₁.ne'
  have hv_cont : Continuous (fun g : Aˣ => R g v) :=
    hR.comp (continuous_id.prodMk continuous_const)
  have hi : Integrable (fun g : Aˣ => κ g⁻¹ • R g v) μ :=
    ((hκ.comp continuous_inv).smul hv_cont).integrable_of_hasCompactSupport
      ((hκc.comp_homeomorph (Homeomorph.inv Aˣ)).smul_right)
  let ℓ : E →L[ℝ] ℝ := Complex.reCLM.comp (L.restrictScalars ℝ)
  have he : ℓ (T v) = ∫ g, a g ∂μ := by
    rw [smoothedOperator_apply, smoothedVector, ← ℓ.integral_comp_comm hi]
    apply integral_congr_ae
    filter_upwards with g
    rw [show κ g⁻¹ • R g v = b g⁻¹ • R g v from algebraMap_smul ℂ (b g⁻¹) (R g v), map_smul]
    rfl
  change L (T v) = 0 at hzero
  have hz : ℓ (T v) = 0 := by
    change (L (T v)).re = 0
    rw [hzero, Complex.zero_re]
  exact hpos.ne' (he.symm.trans hz)

end Units

/-- For a jointly continuous Banach action of the units of a finite-dimensional real Banach
algebra, inverse precomposition on the norm-continuous dual gives a jointly continuous
Banach action whose functionals separate the original space. -/
def NormContinuousDualStatement : Prop :=
  ∀ {A E : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [FiniteDimensional ℝ A] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (R : Aˣ →* (E →L[ℂ] E)), IsContinuousRepresentation R →
    IsClosed (space R : Set (StrongDual ℂ E)) ∧
    IsContinuousRepresentation (representation R) ∧
    ∀ v : E, v ≠ 0 → ∃ L : space R, L.val v ≠ 0

theorem normContinuousDual : NormContinuousDualStatement := by
  intro A E _ _ _ _ _ _ _ R hR
  let : LocallyCompactSpace Aˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  exact ⟨isClosed_space R hR, isContinuousRepresentation R hR, fun _ => separates R hR⟩

end Langlands.Archimedean.NormContinuousDual
