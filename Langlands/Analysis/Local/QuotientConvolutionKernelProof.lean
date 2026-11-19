import Langlands.Analysis.Local.QuotientConvolutionKernelStatement
import Langlands.Analysis.Local.QuotientL2UnfoldingProof

noncomputable section

universe uG

namespace Langlands.QuotientIntegration

open MeasureTheory Filter Topology
open scoped CompactlySupported Pointwise

section Kernel

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) [MeasurableSpace H] [BorelSpace H]
  (μH : Measure H) [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]

omit [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
/-- An orbit integral of a bounded weight vanishing off `K` is bounded by the
subgroup measure of a compact set containing all quotients `b c⁻¹` of points
of `K`. -/
theorem orbitIntegral_norm_le (hH : IsClosed (H : Set G))
    (k : G → ℂ) (K D : Set G) (hD : IsCompact D)
    (hK : ∀ b, b ∉ K → k b = 0) (hKD : ∀ b ∈ K, ∀ c ∈ K, b * c⁻¹ ∈ D)
    (B : ℝ) (hB : ∀ b, ‖k b‖ ≤ B) (y : G) :
    ∫ η : H, ‖k (η.val * y)‖ ∂μH ≤ B * μH.real (Subtype.val ⁻¹' D) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1)
  have hDc : IsCompact (Subtype.val ⁻¹' D : Set H) :=
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage hD
  by_cases hex : ∃ η₀ : H, η₀.val * y ∈ K
  · obtain ⟨η₀, hη₀⟩ := hex
    set A : Set H := (fun η => η * η₀⁻¹) ⁻¹' (Subtype.val ⁻¹' D) with hAdef
    have hAm : MeasurableSet A :=
      (hDc.isClosed.preimage (continuous_id.mul continuous_const)).measurableSet
    have hAeq : μH A = μH (Subtype.val ⁻¹' D) := measure_preimage_mul_right μH η₀⁻¹ _
    have hAfin : μH A < ⊤ := by
      rw [hAeq]
      exact hDc.measure_lt_top
    have hbound : ∀ η : H, ‖k (η.val * y)‖ ≤ A.indicator (fun _ => B) η := by
      intro η
      by_cases hη : η.val * y ∈ K
      · have hA : η ∈ A := by
          change (η * η₀⁻¹).val ∈ D
          have h := hKD _ hη _ hη₀
          simpa [mul_assoc] using h
        rw [Set.indicator_of_mem hA]
        exact hB _
      · rw [hK _ hη, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => hB0) _
    calc ∫ η : H, ‖k (η.val * y)‖ ∂μH
        ≤ ∫ η : H, A.indicator (fun _ => B) η ∂μH :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            ((integrableOn_const hAfin.ne).integrable_indicator hAm)
            (Eventually.of_forall hbound)
      _ = B * μH.real (Subtype.val ⁻¹' D) := by
          rw [integral_indicator hAm, setIntegral_const, smul_eq_mul, mul_comm,
            measureReal_def, measureReal_def, hAeq]
  · simp only [not_exists] at hex
    have hz : ∀ η : H, ‖k (η.val * y)‖ = 0 := fun η => by rw [hK _ (hex η), norm_zero]
    simp only [hz, integral_zero]
    exact mul_nonneg hB0 measureReal_nonneg

variable [SFinite μH] [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
  (μG : Measure G) [IsFiniteMeasureOnCompacts μG]
  (ν : Measure (LeftQuotient H))

omit [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G] [SFinite μH]
  [BorelSpace (LeftQuotient H)] [IsFiniteMeasureOnCompacts μG] in
/-- An `L²` vector representing the quotient average of a bounded compactly
supported weight vanishing off `K` has squared norm at most the bound, the
subgroup measure of `D` and the `L¹` norm of the weight. -/
theorem quotientAverageVector_norm_sq_le (hH : IsClosed (H : Set G))
    (hν : IsCompatible H μG μH ν) (k : C_c(G, ℂ)) (w : Lp ℂ 2 ν)
    (hw : (w : LeftQuotient H → ℂ) =ᵐ[ν] quotientAverage H μH k)
    (K D : Set G) (hD : IsCompact D)
    (hK : ∀ b, b ∉ K → k b = 0) (hKD : ∀ b ∈ K, ∀ c ∈ K, b * c⁻¹ ∈ D)
    (B : ℝ) (hB : ∀ b, ‖k b‖ ≤ B) :
    ‖w‖ ^ 2 ≤ B * μH.real (Subtype.val ⁻¹' D) * ∫ b, ‖k b‖ ∂μG := by
  set C : ℝ := B * μH.real (Subtype.val ⁻¹' D) with hCdef
  -- The norm weight and its quotient average.
  set F : G → ℂ := fun b => ((‖k b‖ : ℝ) : ℂ) with hFdef
  have hFc : Continuous F := Complex.continuous_ofReal.comp k.continuous.norm
  have hFs : HasCompactSupport F := k.hasCompactSupport.norm.comp_left Complex.ofReal_zero
  have hpt : ∀ q : LeftQuotient H,
      ‖quotientAverage H μH k q‖ ≤ (quotientAverage H μH F q).re ∧
        (quotientAverage H μH F q).re ≤ C := by
    intro q
    induction q using Quotient.inductionOn with
    | h y =>
      rw [quotientAverage_mk, quotientAverage_mk]
      have hre : (∫ η : H, F (η.val * y) ∂μH).re = ∫ η : H, ‖k (η.val * y)‖ ∂μH := by
        simp only [hFdef]
        rw [integral_complex_ofReal, Complex.ofReal_re]
      rw [hre]
      exact ⟨norm_integral_le_integral_norm _,
        orbitIntegral_norm_le H μH hH k K D hD hK hKD B hB y⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans ((hpt (leftQuotientMap H 1)).1.trans
    (hpt (leftQuotientMap H 1)).2)
  have hFint := hν.averaging_integrable F hFc hFs
  have hFint' : Integrable (fun q => (quotientAverage H μH F q).re) ν := by
    have h := hFint.re
    simp only [RCLike.re_to_complex] at h
    exact h
  have hFre : ∫ q, (quotientAverage H μH F q).re ∂ν = (∫ q, quotientAverage H μH F q ∂ν).re := by
    have h := integral_re hFint
    simp only [RCLike.re_to_complex] at h
    exact h
  -- The `L²` norm as an integral.
  have hnorm : ‖w‖ ^ 2 = ∫ q, ‖w q‖ ^ 2 ∂ν := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) w, L2.inner_def,
      ← integral_re (L2.integrable_inner w w)]
    congr 1
    funext q
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (w q)
  have hint : Integrable (fun q => ‖w q‖ ^ 2) ν := by
    refine (L2.integrable_inner (𝕜 := ℂ) w w).re.congr (Eventually.of_forall fun q => ?_)
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (w q)
  rw [hnorm]
  calc ∫ q, ‖w q‖ ^ 2 ∂ν
      ≤ ∫ q, C * (quotientAverage H μH F q).re ∂ν := by
        refine integral_mono_ae hint (hFint'.const_mul C) ?_
        filter_upwards [hw] with q hq
        rw [hq]
        obtain ⟨h1, h2⟩ := hpt q
        have h0 := norm_nonneg (quotientAverage H μH k q)
        nlinarith
    _ = C * ∫ b, ‖k b‖ ∂μG := by
        rw [integral_const_mul, hFre, hν.integral_formula F hFc hFs]
        simp only [hFdef]
        rw [integral_complex_ofReal, Complex.ofReal_re]

end Kernel

/-- Continuous kernel vectors for compactly supported convolution on a left
coset space with a compatible quotient measure. -/
theorem quotientConvolutionKernel : QuotientConvolutionKernelStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ H hH _ _ μH _ _ _ _ _ μG _ _ ν _ hν f
  -- The translated conjugate weights `b ↦ conj f (x⁻¹ b)`.
  let hfun : G → C_c(G, ℂ) := fun x =>
    { toFun := fun b => star (f (x⁻¹ * b))
      continuous_toFun := (f.continuous.comp (continuous_const.mul continuous_id)).star
      hasCompactSupport' :=
        (f.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft x⁻¹)).comp_left
          (star_zero _) }
  have hfun_apply : ∀ x b, hfun x b = star (f (x⁻¹ * b)) := fun _ _ => rfl
  have hunf := fun x => quotientL2Unfolding H hH μH μG ν hν (hfun x)
  choose _hc _hs v _ℓ hvA hvφ using hunf
  -- Pairing formula and integrability.
  have hpair : ∀ (x : G) (φ : Lp ℂ 2 ν),
      Integrable (fun a => f a * φ (leftQuotientMap H (x * a))) μG ∧
        inner ℂ (v x) φ = ∫ a, f a * φ (leftQuotientMap H (x * a)) ∂μG := by
    intro x φ
    obtain ⟨hI, -, hE⟩ := hvφ x φ
    have hcomp : (fun a => f a * φ (leftQuotientMap H (x * a))) =
        fun a => (fun g => star (hfun x g) * φ (leftQuotientMap H g)) (x * a) := by
      funext a
      simp only [hfun_apply, star_star, inv_mul_cancel_left]
    refine ⟨?_, ?_⟩
    · rw [hcomp]
      exact hI.comp_mul_left x
    · rw [hE, hcomp]
      exact (integral_mul_left_eq_self _ x).symm
  -- The norm bound for one vector.
  have hbound : ∀ (x : G) (M : ℝ), (∀ a, ‖f a‖ ≤ M) →
      ‖v x‖ ^ 2 ≤ M * (∫ a, ‖f a‖ ∂μG) *
        μH.real (Subtype.val ⁻¹'
          ((fun s => x * s * x⁻¹) '' (tsupport f * (tsupport f)⁻¹))) := by
    intro x M hM
    set T : Set G := tsupport f
    have hT : IsCompact T := f.hasCompactSupport
    set K : Set G := (fun s => x * s) '' T
    set D : Set G := (fun s => x * s * x⁻¹) '' (T * T⁻¹)
    have hD : IsCompact D :=
      (hT.mul hT.inv).image ((continuous_const.mul continuous_id).mul continuous_const)
    have hK : ∀ b, b ∉ K → hfun x b = 0 := by
      intro b hb
      rw [hfun_apply]
      by_contra hne
      apply hb
      have hs : x⁻¹ * b ∈ T := subset_tsupport _ (fun h0 => hne (by rw [h0, star_zero]))
      exact ⟨x⁻¹ * b, hs, mul_inv_cancel_left x b⟩
    have hKD : ∀ b ∈ K, ∀ c ∈ K, b * c⁻¹ ∈ D := by
      rintro _ ⟨s₁, hs₁, rfl⟩ _ ⟨s₂, hs₂, rfl⟩
      exact ⟨s₁ * s₂⁻¹, Set.mul_mem_mul hs₁ (Set.inv_mem_inv.2 hs₂), by group⟩
    have hB : ∀ b, ‖hfun x b‖ ≤ M := fun b => by
      rw [hfun_apply, norm_star]
      exact hM _
    have h := quotientAverageVector_norm_sq_le H μH μG ν hH hν (hfun x) (v x) (hvA x)
      K D hD hK hKD M hB
    have hL1 : ∫ b, ‖hfun x b‖ ∂μG = ∫ a, ‖f a‖ ∂μG := by
      have hl := integral_mul_left_eq_self (μ := μG) (fun b => ‖hfun x b‖) x
      rw [← hl]
      congr 1
      funext a
      rw [hfun_apply, norm_star, inv_mul_cancel_left]
    rw [hL1] at h
    linarith [h, mul_right_comm M (μH.real (Subtype.val ⁻¹' D)) (∫ a, ‖f a‖ ∂μG)]
  refine ⟨v, ?_, hpair, hbound⟩
  -- Continuity.
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨W, hWc, hW⟩ := exists_compact_mem_nhds x₀
  set T : Set G := tsupport f
  have hT : IsCompact T := f.hasCompactSupport
  set K : Set G := W * T
  have hKc : IsCompact K := hWc.mul hT
  set D : Set G := K * K⁻¹
  have hDc : IsCompact D := hKc.mul hKc.inv
  set C : ℝ := μH.real (Subtype.val ⁻¹' D) * μG.real K
  have hC0 : 0 ≤ C := mul_nonneg measureReal_nonneg measureReal_nonneg
  set ε : ℝ := δ / (Real.sqrt C + 1) / 2
  have hε : 0 < ε := by positivity
  let := IsTopologicalGroup.rightUniformSpace G
  have ha := f.hasCompactSupport.uniformContinuous_of_continuous f.continuous
  rw [uniformContinuous_iff_eventually] at ha
  obtain ⟨U, hU, hfU⟩ := ha _ (Metric.dist_mem_uniformity hε)
  have hU' : {x | x₀⁻¹ * x ∈ U} ∈ 𝓝 x₀ := by
    refine (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds ?_
    simpa using hU
  filter_upwards [hW, hU'] with x hxW hxU
  -- The difference weight.
  set k : C_c(G, ℂ) := hfun x - hfun x₀
  have hk : ∀ b, k b = star (f (x⁻¹ * b)) - star (f (x₀⁻¹ * b)) := fun b => rfl
  have hkε : ∀ b, ‖k b‖ ≤ ε := by
    intro b
    rw [hk, ← star_sub, norm_star, ← dist_eq_norm]
    have h := @hfU ⟨x⁻¹ * b, x₀⁻¹ * b⟩ (by simpa [mul_assoc] using hxU)
    exact h.le
  have hkK : ∀ b, b ∉ K → k b = 0 := by
    intro b hb
    have hz : ∀ y ∈ W, f (y⁻¹ * b) = 0 := by
      intro y hy
      by_contra hne
      exact hb ⟨y, hy, y⁻¹ * b, subset_tsupport _ hne, mul_inv_cancel_left y b⟩
    rw [hk, hz x hxW, hz x₀ (mem_of_mem_nhds hW), star_zero, sub_zero]
  have hKD : ∀ b ∈ K, ∀ c ∈ K, b * c⁻¹ ∈ D := fun b hb c hc =>
    Set.mul_mem_mul hb (Set.inv_mem_inv.2 hc)
  -- Its unfolding vector is the difference of the two vectors.
  obtain ⟨-, -, w, _ℓw, hwA, hwφ⟩ := quotientL2Unfolding H hH μH μG ν hν k
  have hweq : w = v x - v x₀ := by
    refine ext_inner_right ℂ fun φ => ?_
    rw [inner_sub_left, (hwφ φ).2.2, (hvφ x φ).2.2, (hvφ x₀ φ).2.2,
      ← integral_sub (hvφ x φ).1 (hvφ x₀ φ).1]
    congr 1
    funext g
    rw [hk, star_sub, star_star, star_star, sub_mul, hfun_apply, hfun_apply, star_star,
      star_star]
  have hw2 := quotientAverageVector_norm_sq_le H μH μG ν hH hν k w hwA K D hDc hkK hKD
    ε hkε
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hL1 : ∫ b, ‖k b‖ ∂μG ≤ ε * μG.real K := by
    have hKfin : μG K < ⊤ := hKc.measure_lt_top
    calc ∫ b, ‖k b‖ ∂μG ≤ ∫ b, K.indicator (fun _ => ε) b ∂μG := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            ((integrableOn_const hKfin.ne).integrable_indicator hKm)
            (Eventually.of_forall fun b => ?_)
          by_cases hb : b ∈ K
          · rw [Set.indicator_of_mem hb]
            exact hkε b
          · rw [Set.indicator_of_notMem hb]
            show ‖k b‖ ≤ 0
            rw [hkK b hb, norm_zero]
      _ = ε * μG.real K := by
          rw [integral_indicator hKm, setIntegral_const, smul_eq_mul, mul_comm]
  have hsq : ‖v x - v x₀‖ ^ 2 ≤ ε ^ 2 * C := by
    rw [← hweq]
    calc ‖w‖ ^ 2 ≤ ε * μH.real (Subtype.val ⁻¹' D) * ∫ b, ‖k b‖ ∂μG := hw2
      _ ≤ ε * μH.real (Subtype.val ⁻¹' D) * (ε * μG.real K) :=
          mul_le_mul_of_nonneg_left hL1 (mul_nonneg hε.le measureReal_nonneg)
      _ = ε ^ 2 * C := by ring
  have hs : 0 ≤ Real.sqrt C := Real.sqrt_nonneg _
  have hCs : C = Real.sqrt C ^ 2 := (Real.sq_sqrt hC0).symm
  have hεs : ε * Real.sqrt C ≤ δ / 2 := by
    have h1 : Real.sqrt C / (Real.sqrt C + 1) ≤ 1 :=
      (div_le_one (by positivity)).2 (by linarith)
    calc ε * Real.sqrt C = δ / 2 * (Real.sqrt C / (Real.sqrt C + 1)) := by
          simp only [ε]
          field_simp
      _ ≤ δ / 2 * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = δ / 2 := mul_one _
  have hlt : ‖v x - v x₀‖ ^ 2 < δ ^ 2 := by
    calc ‖v x - v x₀‖ ^ 2 ≤ ε ^ 2 * C := hsq
      _ = (ε * Real.sqrt C) ^ 2 := by rw [mul_pow, ← hCs]
      _ ≤ (δ / 2) ^ 2 := pow_le_pow_left₀ (mul_nonneg hε.le hs) hεs 2
      _ < δ ^ 2 := by nlinarith
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hδ.le hlt

end Langlands.QuotientIntegration
