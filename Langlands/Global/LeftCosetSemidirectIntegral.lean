import Langlands.Global.LeftCosetSemidirectPeriod

/-! # Normalized periods for split lattices in semidirect products -/

noncomputable section

universe u v w

open MeasureTheory Set Topology
open scoped ENNReal NNReal Pointwise

set_option autoImplicit false

namespace Langlands.Global.LeftCosetSpace

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Integration on a rational fundamental domain, with Haar mass normalized to one
when the domain has positive finite Haar measure. -/
def normalizedFundamentalDomainIntegral (Γ : Subgroup G) (hΓ : IsDiscrete (Γ : Set G))
    (φ : G → ℂ) : ℂ :=
  ((Measure.haar : Measure G) (fundamentalDomain Γ hΓ)).toReal⁻¹ •
    ∫ x in fundamentalDomain Γ hΓ, φ x ∂Measure.haar

namespace Semidirect

variable {N : Type u} {M : Type v} {H : Type w} [Group N] [Group M] [Group H]
  (i : N →* H) (j : M →* H) (p : H →* M)
  (hpj : ∀ m, p (j m) = m)
  (hker : ∀ h, p h = 1 → ∃ n, i n = h)
  (hpi : ∀ n, p (i n) = 1)
  [TopologicalSpace N] [TopologicalSpace M] [TopologicalSpace H]
  [IsTopologicalGroup N] [IsTopologicalGroup M] [IsTopologicalGroup H]
  [SecondCountableTopology N] [SecondCountableTopology M] [SecondCountableTopology H]
  [LocallyCompactSpace N] [LocallyCompactSpace M] [LocallyCompactSpace H]
  [MeasurableSpace N] [MeasurableSpace M] [MeasurableSpace H]
  [BorelSpace N] [BorelSpace M] [BorelSpace H]
  (hi : IsEmbedding i) (hj : Continuous j) (hp : Continuous p)
  (Γ : Subgroup H) (hΓ : IsDiscrete (Γ : Set H))
  (ΓM : Subgroup M) (hΓM : IsDiscrete (ΓM : Set M))
  (hjΓ : ∀ m ∈ ΓM, j m ∈ Γ) (hpΓ : ∀ h ∈ Γ, p h ∈ ΓM)

include hpj hker hpi hi hj hp hjΓ hpΓ in
/-- The normalized period on a compact split quotient is the iterated normalized period
over the normal and complement quotients. -/
theorem normalizedFundamentalDomainIntegral_eq_iterated
    (ΓN : Subgroup N) (hΓN : IsDiscrete (ΓN : Set N))
    (hiΓ : ∀ n, i n ∈ Γ ↔ n ∈ ΓN)
    [CompactSpace (Langlands.Global.LeftCosetSpace ΓN)]
    [CompactSpace (Langlands.Global.LeftCosetSpace ΓM)]
    [CompactSpace (Langlands.Global.LeftCosetSpace Γ)]
    (φ : H → ℂ) (hφ : Continuous φ)
    (hφΓ : ∀ γ ∈ Γ, ∀ h, φ (γ * h) = φ h) :
    normalizedFundamentalDomainIntegral Γ hΓ φ =
      normalizedFundamentalDomainIntegral ΓM hΓM fun m =>
        normalizedFundamentalDomainIntegral ΓN hΓN fun n => φ (i n * j m) := by
  classical
  have heq : Γ.comap i = ΓN := Subgroup.ext hiΓ
  subst ΓN
  let ΓN := Γ.comap i
  let EN := fundamentalDomain ΓN hΓN
  let EM := fundamentalDomain ΓM hΓM
  let EH := fundamentalDomain Γ hΓ
  let Φ := prodHomeomorph i j p hpj hker hpi hi hj hp
  let ν := (Measure.haar : Measure N).prod (Measure.haar : Measure M)
  have := isLocallyFiniteMeasure_haarQuotientMeasure ΓN hΓN
  have := isLocallyFiniteMeasure_haarQuotientMeasure ΓM hΓM
  have := isLocallyFiniteMeasure_haarQuotientMeasure Γ hΓ
  obtain ⟨c, hc⟩ := exists_haar_eq_smul_map_prod hpj hker hpi hi hj hp
    (mulEquivHaarChar_conj_eq_one_of_finiteCovolume
      i j p hpj hker hpi hi hj Γ ΓM hΓM hjΓ hΓN)
  have hEN := haar_fundamentalDomain_ne_top ΓN hΓN
  have hEM := haar_fundamentalDomain_ne_top ΓM hΓM
  have hEH := haar_fundamentalDomain_ne_top Γ hΓ
  have : IsFiniteMeasure ((Measure.haar : Measure N).restrict EN) := ⟨by simpa [EN] using hEN.lt_top⟩
  have : IsFiniteMeasure ((Measure.haar : Measure M).restrict EM) := ⟨by simpa [EM] using hEM.lt_top⟩
  let f := lift Γ φ (fun γ h => hφΓ γ γ.property h)
  have hf : Continuous f := continuous_lift Γ _ _ hφ
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  have hI : IntegrableOn (fun x : N × M => φ (Φ x)) (EN ×ˢ EM) ν := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact ⟨(hφ.comp Φ.continuous).stronglyMeasurable.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (ae_of_all _ fun x => hC (mk Γ (Φ x)) (mem_univ _))⟩
  have hdomain := isFundamentalDomain_product
    i j p hpj hker hpi hi hj hp Γ ΓM hΓM hjΓ hpΓ hΓN
  have : Countable Γ := countable_of_isDiscrete Γ hΓ
  have hIeq :
      ∫ h in EH, φ h ∂Measure.haar =
        c • (∫ m in EM, ∫ n in EN, φ (i n * j m) ∂Measure.haar ∂Measure.haar) := by
    rw [(isFundamentalDomain Γ hΓ Measure.haar).setIntegral_eq hdomain
      (fun γ h => hφΓ γ γ.property h)]
    rw [hc, Measure.restrict_smul, integral_smul_nnreal_measure]
    change c • (∫ h in Φ '' (EN ×ˢ EM), φ h ∂ν.map Φ) = _
    rw [Φ.isClosedEmbedding.setIntegral_map, Φ.preimage_image, ← Measure.prod_restrict]
    rw [IntegrableOn, ← Measure.prod_restrict] at hI
    rw [integral_prod_symm _ hI]
    rfl
  have hS : MeasurableSet (Φ '' (EN ×ˢ EM)) := by
    rw [Φ.image_eq_preimage_symm]
    exact Φ.symm.continuous.measurable
      ((measurableSet_fundamentalDomain ΓN hΓN).prod (measurableSet_fundamentalDomain ΓM hΓM))
  have hmass :
      (Measure.haar : Measure H) EH =
        (c : ℝ≥0∞) * (Measure.haar : Measure N) EN * (Measure.haar : Measure M) EM := by
    rw [(isFundamentalDomain Γ hΓ Measure.haar).measure_eq hdomain]
    rw [hc, Measure.smul_apply, Measure.map_apply Φ.continuous.measurable hS,
      Φ.preimage_image, Measure.prod_prod, ENNReal.smul_def, smul_eq_mul, mul_assoc]
  have hmassN : ((Measure.haar : Measure N) EN).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨haar_fundamentalDomain_ne_zero ΓN hΓN, hEN⟩
  have hmassM : ((Measure.haar : Measure M) EM).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨haar_fundamentalDomain_ne_zero ΓM hΓM, hEM⟩
  have hmassH : ((Measure.haar : Measure H) EH).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨haar_fundamentalDomain_ne_zero Γ hΓ, hEH⟩
  have hmassReal :
      ((Measure.haar : Measure H) EH).toReal =
        (c : ℝ) * ((Measure.haar : Measure N) EN).toReal *
          ((Measure.haar : Measure M) EM).toReal := by
    rw [hmass, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]
  have hc0 : (c : ℝ) ≠ 0 := by
    intro hz
    apply hmassH
    rw [hmassReal, hz, zero_mul, zero_mul]
  unfold normalizedFundamentalDomainIntegral
  change ((Measure.haar : Measure H) EH).toReal⁻¹ •
      (∫ h in EH, φ h ∂Measure.haar) =
    ((Measure.haar : Measure M) EM).toReal⁻¹ •
      ∫ m in EM, ((Measure.haar : Measure N) EN).toReal⁻¹ •
        (∫ n in EN, φ (i n * j m) ∂Measure.haar) ∂Measure.haar
  rw [hIeq, integral_smul, NNReal.smul_def, ← mul_smul, ← mul_smul, hmassReal]
  congr 1
  field_simp

end Semidirect

end Langlands.Global.LeftCosetSpace
