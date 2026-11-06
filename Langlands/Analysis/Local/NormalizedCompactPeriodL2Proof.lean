import Langlands.Analysis.Local.CompactPeriodL2PairingProof
import Langlands.Analysis.Local.CompactQuotientPeriod
import Langlands.Global.RelativelyCompactFundamentalDomainProof
import Langlands.Analysis.Local.CompactTestSeparationProof
import Langlands.Analysis.Local.ModularCharacterContinuity
import Langlands.Analysis.Local.NormalizedCompactPeriodL2Statement

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure Set Topology
open Langlands.Global
open scoped CompactlySupported ENNReal

universe uG uH

section Translation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

private theorem period_map_left_invHaar (a : G) :
    Measure.map (fun g => a * g) μ.inv = modularCharacter a⁻¹ • μ.inv := by
  have hswap : Measure.map (fun g => a * g) μ.inv =
      (Measure.map (fun g => g * a⁻¹) μ).inv := by
    rw [Measure.inv_def, Measure.inv_def,
      Measure.map_map (measurable_const_mul a) measurable_inv,
      Measure.map_map measurable_inv (measurable_mul_const a⁻¹)]
    congr 1
    funext g
    simp
  rw [hswap, map_right_mul_eq_modularCharacterFun_smul,
    Measure.inv_def, Measure.map_smul _ measurable_inv.aemeasurable]
  rfl

private theorem period_integrable_left_pullback_iff
    (a : G) (F : G → ℂ) (hF : StronglyMeasurable F) :
    Integrable (fun g => F (a⁻¹ * g)) μ.inv ↔ Integrable F μ.inv := by
  change Integrable (F ∘ fun g => a⁻¹ * g) μ.inv ↔ Integrable F μ.inv
  rw [← integrable_map_measure hF.aestronglyMeasurable
    (measurable_const_mul a⁻¹).aemeasurable, period_map_left_invHaar, inv_inv]
  exact integrable_smul_measure
    (c := (modularCharacter a : ℝ≥0∞))
    (ENNReal.coe_ne_zero.mpr (ne_of_gt (modularCharacterFun_pos a))) ENNReal.coe_ne_top

private theorem period_integral_left_pullback_real
    (a : G) (F : G → ℝ) (hF : StronglyMeasurable F) :
    (∫ g, F (a⁻¹ * g) ∂μ.inv) =
      (modularCharacter a : ℝ) * ∫ g, F g ∂μ.inv := by
  rw [← integral_map_of_stronglyMeasurable (measurable_const_mul a⁻¹) hF,
    period_map_left_invHaar, inv_inv, integral_smul_nnreal_measure]
  rfl

/-- The actual right-Haar Jacobian transfers product integrability before Fubini. -/
private theorem period_integrable_joint_translate
    {X : Type uH} [MeasurableSpace X] (η : Measure X) [SFinite η]
    (a : X → G) (R A : G × X → ℂ) (hR : Integrable R (μ.inv.prod η))
    (hA : StronglyMeasurable A)
    (hrel : ∀ g x, A ((a x)⁻¹ * g, x) =
      ((modularCharacter (a x) : ℝ) : ℂ) * R (g, x)) :
    Integrable A (μ.inv.prod η) := by
  have hAfiber (x : X) : StronglyMeasurable (fun g => A (g, x)) :=
    hA.comp_measurable (measurable_id.prodMk measurable_const)
  have hAint : ∀ᵐ x ∂η, Integrable (fun g => A (g, x)) μ.inv := by
    filter_upwards [hR.prod_left_ae] with x hx
    apply (period_integrable_left_pullback_iff μ (a x) _ (hAfiber x)).mp
    exact (hx.const_mul ((modularCharacter (a x) : ℝ) : ℂ)).congr
      (Filter.Eventually.of_forall fun g => (hrel g x).symm)
  have hnorm (x : X) :
      (∫ g, ‖A (g, x)‖ ∂μ.inv) = ∫ g, ‖R (g, x)‖ ∂μ.inv := by
    have hp : 0 < (modularCharacter (a x) : ℝ) :=
      modularCharacterFun_pos (a x)
    have hchange := period_integral_left_pullback_real μ (a x)
      (fun g => ‖A (g, x)‖) (hAfiber x).norm
    have hscale : (∫ g, ‖A ((a x)⁻¹ * g, x)‖ ∂μ.inv) =
        (modularCharacter (a x) : ℝ) * ∫ g, ‖R (g, x)‖ ∂μ.inv := by
      calc
        _ = ∫ g, (modularCharacter (a x) : ℝ) * ‖R (g, x)‖ ∂μ.inv := by
          apply integral_congr_ae
          filter_upwards with g
          rw [hrel, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
        _ = _ := integral_const_mul _ _
    exact mul_left_cancel₀ (ne_of_gt hp) (hchange.symm.trans hscale)
  exact (integrable_prod_iff' hA.aestronglyMeasurable).2
    ⟨hAint, hR.integral_norm_prod_right.congr
      (Filter.Eventually.of_forall fun x => (hnorm x).symm)⟩

end Translation

section CompactDomain

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G))
  [MeasurableSpace Γ] [BorelSpace Γ]
  (μΓ : Measure Γ) [SFinite μΓ] [μΓ.IsMulRightInvariant]
  [IsFiniteMeasureOnCompacts μΓ]
  [MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]
  (ν : Measure (LeftQuotient Γ)) [IsFiniteMeasureOnCompacts ν]
  (hν : IsCompatible Γ μ.inv μΓ ν)
  {H : Type uH} [TopologicalSpace H] [T2Space H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
  (μH : Measure H) [IsFiniteMeasureOnCompacts μH]

include hΓ hν in
private theorem compactPeriod_translated_test
    (s : Set H) (hs : MeasurableSet s) (hsc : IsCompact (closure s))
    (j : H → G) (hj : Continuous j) (c : H → ℂ) (hc : Continuous c)
    (f : C_c(G, ℂ)) :
    ∃ ℓ : Lp ℂ 2 ν →L[ℂ] ℂ, ∀ φ : Lp ℂ 2 ν,
      Integrable (fun p : G × H => c p.2 * star (f p.1) *
        φ (leftQuotientMap Γ (j p.2 * p.1))) (μ.inv.prod (μH.restrict s)) ∧
      Integrable (fun g => star (f g) *
        ∫ h in s, c h * φ (leftQuotientMap Γ (j h * g)) ∂μH) μ.inv ∧
      ℓ φ = ∫ g, star (f g) *
        (∫ h in s, c h * φ (leftQuotientMap Γ (j h * g)) ∂μH) ∂μ.inv := by
  have hfinite : μH s < ⊤ := (measure_mono subset_closure).trans_lt hsc.measure_lt_top
  let : IsFiniteMeasure (μH.restrict s) := ⟨by simpa using hfinite⟩
  let d : H → ℂ := fun h => ((modularCharacter (j h) : ℝ) : ℂ)
  have hd : Continuous d := Complex.continuous_ofReal.comp
    (continuous_subtype_val.comp
      (Langlands.Haar.continuous_modularCharacter_of_locallyCompact.comp hj))
  have hdne (h : H) : d h ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (modularCharacterFun_pos (j h)))
  let w : H → ℂ := fun h => star (c h / d h)
  have hw : Continuous w := (hc.div hd hdne).star
  have hwc (h : H) : star (w h) * d h = c h := by
    simp only [w, star_star]
    exact div_mul_cancel₀ _ (hdne h)
  obtain ⟨v, ℓ, _, hpair⟩ :=
    compactPeriodL2Pairing μ Γ hΓ μΓ ν hν μH s hs hsc j hj w hw f
  refine ⟨ℓ, ?_⟩
  intro φ
  let R : G × H → ℂ := fun p =>
    star (w p.2) * star (f ((j p.2)⁻¹ * p.1)) * φ (leftQuotientMap Γ p.1)
  let A : G × H → ℂ := fun p =>
    c p.2 * star (f p.1) * φ (leftQuotientMap Γ (j p.2 * p.1))
  have hAm : StronglyMeasurable A := by
    have hp : Measurable (fun p : G × H =>
        leftQuotientMap Γ (j p.2 * p.1)) :=
      ((leftQuotient_isOpenQuotientMap Γ).continuous.comp
        ((hj.comp continuous_snd).mul continuous_fst)).measurable
    exact (((hc.comp continuous_snd).stronglyMeasurable.mul
      (f.continuous.star.comp continuous_fst).stronglyMeasurable).mul
        ((Lp.stronglyMeasurable φ).comp_measurable hp))
  have hrel (g : G) (h : H) : A ((j h)⁻¹ * g, h) = d h * R (g, h) := by
    simp only [A, R, w, star_star, mul_inv_cancel_left]
    field_simp [hdne h]
  have hA : Integrable A (μ.inv.prod (μH.restrict s)) :=
    period_integrable_joint_translate μ (μH.restrict s) j R A (hpair φ).1 hAm hrel
  have hinner (g : G) : (∫ h in s, A (g, h) ∂μH) =
      star (f g) * ∫ h in s, c h * φ (leftQuotientMap Γ (j h * g)) ∂μH := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with h
    dsimp only [A]
    ring
  refine ⟨hA, hA.integral_prod_left.congr
    (Filter.Eventually.of_forall hinner), ?_⟩
  calc
    ℓ φ = inner ℂ v φ := (hpair φ).2.2.1
    _ = ∫ h in s, star (w h) * d h *
        (∫ g, star (f g) * φ (leftQuotientMap Γ (j h * g)) ∂μ.inv) ∂μH :=
      (hpair φ).2.2.2
    _ = ∫ h in s, ∫ g, A (g, h) ∂μ.inv ∂μH := by
      apply integral_congr_ae
      filter_upwards with h
      rw [hwc, ← integral_const_mul]
      simp only [A, mul_assoc]
    _ = ∫ g, ∫ h in s, A (g, h) ∂μH ∂μ.inv :=
      (integral_integral_swap hA).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hinner)

end CompactDomain

section NormalizedDomain

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G))
  [MeasurableSpace Γ] [BorelSpace Γ]
  (μΓ : Measure Γ) [SFinite μΓ] [μΓ.IsMulRightInvariant]
  [IsFiniteMeasureOnCompacts μΓ]
  [MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]
  (ν : Measure (LeftQuotient Γ)) [IsFiniteMeasureOnCompacts ν]
  (hν : IsCompatible Γ μ.inv μΓ ν)
  {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]
  (Λ : Subgroup H) (hΛ : IsDiscrete (Λ : Set H))
  [BorelSpace (LeftCosetSpace Λ)]
  (μH : Measure H) [SMulInvariantMeasure Λ H μH] [IsFiniteMeasureOnCompacts μH]
  (j : H →* G) (hj : Continuous j) (hjΛ : ∀ η : Λ, j η ∈ Γ)
  (χ : H →* ℂˣ) (hχ : Continuous χ) (hχΛ : ∀ η : Λ, χ η = 1)

include hΓ hν hj hχ in
private theorem normalizedPeriod_test_form
    (s : Set H) (hs : MeasurableSet s) (hsc : IsCompact (closure s))
    (hfd : IsFundamentalDomain Λ s μH) (f : C_c(G, ℂ)) :
    ∃ ℓ : Lp ℂ 2 ν →L[ℂ] ℂ, ∀ φ : Lp ℂ 2 ν,
      Integrable (fun g => star (f g) *
        normalizedQuotientCharacterPeriod Γ Λ j hjΛ χ hχΛ hΛ μH φ g) μ.inv ∧
      ℓ φ = ∫ g, star (f g) *
        normalizedQuotientCharacterPeriod Γ Λ j hjΛ χ hχΛ hΛ μH φ g ∂μ.inv := by
  let c : H → ℂ := fun h => (χ h : ℂ)⁻¹
  have hc : Continuous c :=
    (Units.continuous_val.comp hχ).inv₀ (fun _ => Units.ne_zero _)
  obtain ⟨ℓ, hℓ⟩ :=
    compactPeriod_translated_test μ Γ hΓ μΓ ν hν μH s hs hsc j hj c hc f
  let m : ℂ := (((μH s)⁻¹).toReal : ℂ)
  refine ⟨m • ℓ, ?_⟩
  intro φ
  have heq (g : G) :
      star (f g) *
          normalizedQuotientCharacterPeriod Γ Λ j hjΛ χ hχΛ hΛ μH φ g =
        m * (star (f g) *
          ∫ h in s, c h * φ (LeftCosetSpace.mk Γ (j h * g)) ∂μH) := by
    rw [normalizedQuotientCharacterPeriod_eq_domain Γ Λ j hjΛ χ hχΛ hΛ μH
      hj hχ (Lp.stronglyMeasurable φ) s hfd]
    simp only [Complex.real_smul, m, c]
    ring
  refine ⟨((hℓ φ).2.1.const_mul m).congr
    (Filter.Eventually.of_forall fun g => (heq g).symm), ?_⟩
  change m * ℓ φ = _
  rw [(hℓ φ).2.2, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun g => (heq g).symm)

include hj hχ in
omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace Γ] [BorelSpace Γ]
  [IsFiniteMeasureOnCompacts ν] [T2Space H] [LocallyCompactSpace H]
  [IsFiniteMeasureOnCompacts μH] in
private theorem normalizedPeriod_integrable_iff_domain
    (s : Set H) (hfd : IsFundamentalDomain Λ s μH)
    (hz : μH s ≠ 0) (ht : μH s ≠ ⊤) (φ : Lp ℂ 2 ν) (g : G) :
    HasConvergentQuotientCharacterPeriod Γ Λ j hjΛ χ hχΛ
        (LeftCosetSpace.normalizedMeasure Λ μH (LeftCosetSpace.fundamentalDomain Λ hΛ))
        φ g ↔
      Integrable (fun h => (χ h : ℂ)⁻¹ *
        φ (LeftCosetSpace.mk Γ (j h * g))) (μH.restrict s) := by
  let := LeftCosetSpace.countable_of_isDiscrete Λ hΛ
  unfold HasConvergentQuotientCharacterPeriod
  rw [LeftCosetSpace.normalizedMeasure_eq Λ μH
    (LeftCosetSpace.isFundamentalDomain Λ hΛ μH) hfd,
    LeftCosetSpace.normalizedMeasure,
    integrable_smul_measure (ENNReal.inv_ne_zero.mpr ht) (ENNReal.inv_ne_top.mpr hz)]
  exact LeftCosetSpace.integrable_quotientMeasure_iff Λ μH s _
    (stronglyMeasurable_periodIntegrand Γ Λ j hjΛ χ hχΛ hj hχ
      (Lp.stronglyMeasurable φ) g).aestronglyMeasurable

include hΓ hν hj hχ in
omit [IsTopologicalGroup H] in
private theorem period_ae_domain_converges
    (s : Set H) (hs : MeasurableSet s) (hsc : IsCompact (closure s))
    (φ : Lp ℂ 2 ν) :
    ∀ᵐ g ∂μ.inv, Integrable (fun h => (χ h : ℂ)⁻¹ *
      φ (LeftCosetSpace.mk Γ (j h * g))) (μH.restrict s) := by
  have hcut (n : ℕ) : ∃ f : C_c(G, ℂ),
      EqOn f 1 (compactCovering G n) := by
    obtain ⟨ρ, hρ, _, hρc, _⟩ := exists_continuous_one_zero_of_isCompact
      (isCompact_compactCovering G n) isClosed_empty (disjoint_empty _)
    refine ⟨⟨⟨fun g => (ρ g : ℂ), Complex.continuous_ofReal.comp ρ.continuous⟩,
      hρc.comp_left Complex.ofReal_zero⟩, ?_⟩
    intro g hg
    change (ρ g : ℂ) = 1
    simpa only [Pi.one_apply, Complex.ofReal_one] using congrArg Complex.ofReal (hρ hg)
  choose f hf using hcut
  let c : H → ℂ := fun h => (χ h : ℂ)⁻¹
  have hc : Continuous c :=
    (Units.continuous_val.comp hχ).inv₀ (fun _ => Units.ne_zero _)
  have htest (n : ℕ) : ∀ᵐ g ∂μ.inv,
      Integrable (fun h => c h * star (f n g) *
        φ (leftQuotientMap Γ (j h * g))) (μH.restrict s) :=
    ((compactPeriod_translated_test μ Γ hΓ μΓ ν hν μH s hs hsc j hj c hc (f n)).choose_spec
      φ).1.prod_right_ae
  filter_upwards [ae_all_iff.mpr htest] with g hg
  obtain ⟨n, hn⟩ := exists_mem_compactCovering g
  have hfg : f n g = 1 := by simpa only [Pi.one_apply] using hf n hn
  simpa only [c, hfg, star_one, mul_one, LeftCosetSpace.mk, leftQuotientMap] using hg n

end NormalizedDomain

private theorem period_locallyIntegrable_of_tests
    {G : Type uG} [TopologicalSpace G] [T2Space G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (η : Measure G) (F : G → ℂ)
    (htest : ∀ f : C_c(G, ℂ), Integrable (fun g => star (f g) * F g) η) :
    LocallyIntegrable F η := by
  intro g
  obtain ⟨K, hK, hKg⟩ := exists_compact_mem_nhds g
  obtain ⟨ρ, hρK, _, hρc, _⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty _)
  let f : C_c(G, ℂ) :=
    ⟨⟨fun x => (ρ x : ℂ), Complex.continuous_ofReal.comp ρ.continuous⟩,
      hρc.comp_left Complex.ofReal_zero⟩
  refine ⟨K, hKg, (htest f).integrableOn.congr_fun ?_ hK.measurableSet⟩
  intro x hx
  change star (ρ x : ℂ) * F x = F x
  simp only [hρK hx, Pi.one_apply, Complex.ofReal_one, star_one, one_mul]

/-- Actual normalized compact-period convergence, test forms and closedness. -/
theorem normalizedCompactPeriodL2 : NormalizedCompactPeriodL2Statement.{uG, uH} := by
  intro G _ _ _ _ _ _ _ _ μ _ Γ hΓ _ _ μΓ _ _ _ _ _ ν _ hν
    H _ _ _ _ _ _ _ _ Λ hΛ _ μH _ _ hμH K hK hcover j hj hjΛ χ hχ hχΛ
  dsimp only
  obtain ⟨s, hs, hsc, _, hfd, _, hfinite, _⟩ :=
    LeftCosetSpace.relativelyCompactFundamentalDomain Λ hΛ K hK hcover
  have hzero : μH s ≠ 0 := by
    let := LeftCosetSpace.countable_of_isDiscrete Λ hΛ
    exact IsFundamentalDomain.measure_ne_zero hμH (hfd μH)
  let P := normalizedQuotientCharacterPeriod Γ Λ j hjΛ χ hχΛ hΛ μH
  have hforms (f : C_c(G, ℂ)) : ∃ ℓ : Lp ℂ 2 ν →L[ℂ] ℂ,
      ∀ φ : Lp ℂ 2 ν,
        Integrable (fun g => star (f g) * P φ g) μ.inv ∧
        ℓ φ = ∫ g, star (f g) * P φ g ∂μ.inv :=
    normalizedPeriod_test_form μ Γ hΓ μΓ ν hν Λ hΛ μH j hj hjΛ χ hχ hχΛ
      s hs hsc (hfd μH) f
  choose ℓ hℓ using hforms
  have hlocal (φ : Lp ℂ 2 ν) : LocallyIntegrable (P φ) μ.inv :=
    period_locallyIntegrable_of_tests μ.inv (P φ) (fun f => (hℓ f φ).1)
  have hae (φ : Lp ℂ 2 ν) :
      ∀ᵐ g ∂μ.inv, HasConvergentQuotientCharacterPeriod Γ Λ j hjΛ χ hχΛ
        (LeftCosetSpace.normalizedMeasure Λ μH (LeftCosetSpace.fundamentalDomain Λ hΛ))
        φ g := by
    filter_upwards [period_ae_domain_converges μ Γ hΓ μΓ ν hν μH j hj χ hχ
      s hs hsc φ] with g hg
    exact (normalizedPeriod_integrable_iff_domain Γ ν Λ hΛ μH j hj hjΛ χ hχ hχΛ
      s (hfd μH) hzero (hfinite μH).ne φ g).mpr hg
  have hequiv (φ : Lp ℂ 2 ν) : P φ =ᵐ[μ.inv] 0 ↔ ∀ f : C_c(G, ℂ), ℓ f φ = 0 := by
    rw [(Langlands.Analysis.compactTestSeparation μ.inv (P φ) (hlocal φ)).2]
    exact forall_congr' fun f => by rw [(hℓ f φ).2]
  have hclosed : IsClosed {φ : Lp ℂ 2 ν | P φ =ᵐ[μ.inv] 0} := by
    have heq : {φ : Lp ℂ 2 ν | P φ =ᵐ[μ.inv] 0} =
        ⋂ f : C_c(G, ℂ), {φ : Lp ℂ 2 ν | ℓ f φ = 0} := by
      ext φ
      simpa only [mem_ofPred_eq, mem_iInter] using hequiv φ
    rw [heq]
    exact isClosed_iInter fun f => isClosed_eq (ℓ f).continuous continuous_const
  exact ⟨fun φ => ⟨hae φ, hlocal φ⟩, fun f => ⟨ℓ f, hℓ f⟩, hclosed⟩

end Langlands.QuotientIntegration
