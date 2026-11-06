import Langlands.Analysis.Local.CompactPeriodTestProof
import Langlands.Analysis.Local.QuotientL2UnfoldingProof
import Langlands.Analysis.Local.CompactPeriodL2PairingStatement
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure
open scoped CompactlySupported

universe uG uX

section HaarTranslation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

private theorem map_left_invHaar (a : G) :
    Measure.map (fun g => a * g) μ.inv =
      modularCharacter a⁻¹ • μ.inv := by
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

private theorem integral_rightHaar_left_pullback (a : G) (F : G → ℂ)
    (hF : StronglyMeasurable F) :
    (∫ g, F (a⁻¹ * g) ∂μ.inv) = modularCharacter a • ∫ g, F g ∂μ.inv := by
  rw [← integral_map_of_stronglyMeasurable (measurable_const_mul a⁻¹) hF,
    map_left_invHaar, inv_inv, integral_smul_nnreal_measure]

private theorem integral_rightHaar_shifted_test
    (Γ : Subgroup G) [MeasurableSpace (LeftQuotient Γ)]
    [BorelSpace (LeftQuotient Γ)] (a : G) (f : C_c(G, ℂ))
    (ψ : LeftQuotient Γ → ℂ) (hψ : StronglyMeasurable ψ) :
    (∫ g, star (f (a⁻¹ * g)) * ψ (leftQuotientMap Γ g) ∂μ.inv) =
      ((modularCharacter a : ℝ) : ℂ) *
        ∫ g, star (f g) * ψ (leftQuotientMap Γ (a * g)) ∂μ.inv := by
  let F : G → ℂ := fun g => star (f g) * ψ (leftQuotientMap Γ (a * g))
  have hproj : Measurable (leftQuotientMap Γ) :=
    (leftQuotient_isOpenQuotientMap Γ).continuous.measurable
  have hF : StronglyMeasurable F :=
    f.continuous.stronglyMeasurable.star.mul
      (hψ.comp_measurable (hproj.comp (measurable_const_mul a)))
  have h := integral_rightHaar_left_pullback μ a F hF
  simpa only [F, mul_inv_cancel_left, NNReal.smul_def, Complex.real_smul] using h

end HaarTranslation

section PeriodFubini

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [MeasurableSpace Γ] [BorelSpace Γ]
  (μΓ : Measure Γ) [SFinite μΓ] [μΓ.IsMulRightInvariant]
  [IsFiniteMeasureOnCompacts μΓ]
  (μG : Measure G) [IsFiniteMeasureOnCompacts μG] [SFinite μG]
  [MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]
  (ν : Measure (LeftQuotient Γ)) [IsFiniteMeasureOnCompacts ν]
  {X : Type uX} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  (μX : Measure X) [IsFiniteMeasureOnCompacts μX]

private theorem compactPeriod_pairing_fubini
    (hΓ : IsClosed (Γ : Set G)) (hν : IsCompatible Γ μG μΓ ν)
    (s : Set X) (hs : MeasurableSet s) (hsc : IsCompact (closure s))
    (j : X → G) (hj : Continuous j) (w : X → ℂ) (hw : Continuous w)
    (f : C_c(G, ℂ)) (ψ : LeftQuotient Γ → ℂ)
    (hψm : StronglyMeasurable ψ) (hψ : MemLp ψ 2 ν) :
    Integrable
      (fun p : G × X => star (w p.2) * star (f ((j p.2)⁻¹ * p.1)) *
        ψ (leftQuotientMap Γ p.1)) (μG.prod (μX.restrict s)) ∧
    Integrable (fun x => star (w x) *
      ∫ g, star (f ((j x)⁻¹ * g)) * ψ (leftQuotientMap Γ g) ∂μG) (μX.restrict s) ∧
    (∫ g, star (∫ x in s, w x * f ((j x)⁻¹ * g) ∂μX) *
        ψ (leftQuotientMap Γ g) ∂μG) =
      ∫ x in s, star (w x) *
        (∫ g, star (f ((j x)⁻¹ * g)) * ψ (leftQuotientMap Γ g) ∂μG) ∂μX := by
  have hμs : μX s < ⊤ := (measure_mono subset_closure).trans_lt hsc.measure_lt_top
  let : IsFiniteMeasure (μX.restrict s) := ⟨by simpa using hμs⟩
  let fN : C_c(G, ℂ) :=
    ⟨⟨fun g => (‖f g‖ : ℂ), Complex.continuous_ofReal.comp f.continuous.norm⟩,
      (f.hasCompactSupport.comp_left norm_zero).comp_left Complex.ofReal_zero⟩
  let wN : X → ℂ := fun x => (‖w x‖ : ℂ)
  obtain ⟨_, kN, hkN, _⟩ := compactPeriodTest μX s hs hsc j hj wN
    (Complex.continuous_ofReal.comp hw.norm) fN
  have hknorm : ∀ g, ‖kN g‖ = ∫ x in s, ‖w x‖ * ‖f ((j x)⁻¹ * g)‖ ∂μX := by
    intro g
    have he : kN g = ((∫ x in s, ‖w x‖ * ‖f ((j x)⁻¹ * g)‖ ∂μX : ℝ) : ℂ) := by
      rw [hkN]
      change (∫ x in s, (‖w x‖ : ℂ) * (‖f ((j x)⁻¹ * g)‖ : ℂ) ∂μX) = _
      simp only [← Complex.ofReal_mul, integral_complex_ofReal]
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact integral_nonneg fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  obtain ⟨hN, _⟩ := integrable_compact_quotient_unfolding Γ hΓ μΓ μG ν hν kN ψ hψm hψ
  have hNorm : Integrable (fun g => ‖kN g‖ * ‖ψ (leftQuotientMap Γ g)‖) μG := by
    simpa only [norm_mul, norm_star] using hN.norm
  let R : G × X → ℂ := fun p =>
    star (w p.2) * star (f ((j p.2)⁻¹ * p.1)) * ψ (leftQuotientMap Γ p.1)
  have hproj : Measurable (leftQuotientMap Γ) :=
    (leftQuotient_isOpenQuotientMap Γ).continuous.measurable
  have hWm : StronglyMeasurable (fun p : G × X => star (w p.2)) :=
    ((hw.comp continuous_snd).star).stronglyMeasurable
  have hfm : StronglyMeasurable (fun p : G × X => star (f ((j p.2)⁻¹ * p.1))) :=
    ((f.continuous.comp ((hj.comp continuous_snd).inv.mul continuous_fst)).star).stronglyMeasurable
  have hRm : StronglyMeasurable R :=
    (hWm.mul hfm).mul (hψm.comp_measurable (hproj.comp measurable_fst))
  have hfiber : ∀ g, Integrable (fun x => R (g, x)) (μX.restrict s) := by
    intro g
    have hc : Continuous (fun x => R (g, x)) := by
      change Continuous (fun x =>
        star (w x) * star (f ((j x)⁻¹ * g)) * ψ (leftQuotientMap Γ g))
      exact (hw.star.mul (f.continuous.star.comp (hj.inv.mul_const g))).mul
        (continuous_const : Continuous (fun _ : X => ψ (leftQuotientMap Γ g)))
    exact (hc.continuousOn.integrableOn_compact hsc).mono_set subset_closure
  have hnorm : ∀ g, (∫ x, ‖R (g, x)‖ ∂μX.restrict s) =
      ‖kN g‖ * ‖ψ (leftQuotientMap Γ g)‖ := by
    intro g
    simp only [R, norm_mul, norm_star, integral_mul_const]
    rw [hknorm]
  have hR : Integrable R (μG.prod (μX.restrict s)) := by
    apply (integrable_prod_iff hRm.aestronglyMeasurable).2
    exact ⟨Filter.Eventually.of_forall hfiber,
      hNorm.congr (Filter.Eventually.of_forall fun g => (hnorm g).symm)⟩
  refine ⟨hR, ?_, ?_⟩
  · simpa only [R, mul_assoc, integral_const_mul] using hR.integral_prod_right
  · calc
      _ = ∫ g, ∫ x in s, R (g, x) ∂μX ∂μG := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun g => by
          simp only [R, integral_mul_const]
          congr 1
          calc
            _ = ∫ x in s, star (w x * f ((j x)⁻¹ * g)) ∂μX := integral_conj.symm
            _ = _ := by simp only [star_mul, mul_comm]
      _ = ∫ x in s, ∫ g, R (g, x) ∂μG ∂μX := integral_integral_swap hR
      _ = _ := by simp only [R, mul_assoc, integral_const_mul]

end PeriodFubini

/-- The exact modular-corrected compact-domain L² pairing target. -/
theorem compactPeriodL2Pairing : CompactPeriodL2PairingStatement.{uG, uX} := by
  intro G _ _ _ _ _ _ _ _ μ _ Γ hΓ _ _ μΓ _ _ _ _ _ ν _ hν
    X _ _ _ _ _ _ μX _ s hs hsc j hj w hw f
  obtain ⟨_, k, hk, _⟩ := compactPeriodTest μX s hs hsc j hj w hw f
  have hkfun : (k : G → ℂ) = fun g => ∫ x in s, w x * f ((j x)⁻¹ * g) ∂μX :=
    funext hk
  obtain ⟨_, _, v, ℓ, hv, hpair⟩ :=
    quotientL2Unfolding Γ hΓ μΓ μ.inv ν hν k
  refine ⟨v, ℓ, ?_, ?_⟩
  · simpa only [hkfun] using hv
  · intro φ
    obtain ⟨hJoint, hOuter, hFub⟩ :=
      compactPeriod_pairing_fubini Γ μΓ μ.inv ν μX hΓ hν s hs hsc j hj w hw f φ
        (Lp.stronglyMeasurable φ) (Lp.memLp φ)
    have hcorr :
        (fun x => star (w x) *
          ∫ g, star (f ((j x)⁻¹ * g)) * φ (leftQuotientMap Γ g) ∂μ.inv) =
        (fun x => star (w x) * ((modularCharacter (j x) : ℝ) : ℂ) *
          ∫ g, star (f g) * φ (leftQuotientMap Γ (j x * g)) ∂μ.inv) := by
      funext x
      rw [integral_rightHaar_shifted_test μ Γ (j x) f φ (Lp.stronglyMeasurable φ),
        mul_assoc]
    refine ⟨hJoint, ?_, (hpair φ).2.1, ?_⟩
    · rw [← hcorr]
      exact hOuter
    · calc
        inner ℂ v φ = ∫ g, star (k g) * φ (leftQuotientMap Γ g) ∂μ.inv :=
          (hpair φ).2.2
        _ = ∫ x in s, star (w x) *
            (∫ g, star (f ((j x)⁻¹ * g)) * φ (leftQuotientMap Γ g) ∂μ.inv) ∂μX := by
          simpa only [hkfun] using hFub
        _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun x => congrFun hcorr x)

end Langlands.QuotientIntegration
