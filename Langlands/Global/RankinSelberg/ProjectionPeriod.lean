import Langlands.Global.LeftCosetSemidirectPeriod

/-! # Iterated normalized periods over split lattices in semidirect products -/

noncomputable section

universe u v w

open MeasureTheory Set Topology
open scoped ENNReal NNReal Pointwise

namespace Langlands.Global.LeftCosetSpace.Semidirect

variable {N : Type u} {M : Type v} {H : Type w}
  [Group N] [Group M] [Group H]
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
/-- The normalized period of a bounded continuous lattice-invariant function over `Γ \ H` is
the normalized period over `ΓM \ M` of its normalized periods over `ΓN \ N`. -/
theorem normalizedPeriod_eq_iterated
    (hΓN : IsDiscrete ((Γ.comap i : Subgroup N) : Set N))
    [IsFiniteMeasure (haarQuotientMeasure (Γ.comap i) hΓN)]
    [IsFiniteMeasure (haarQuotientMeasure ΓM hΓM)]
    (φ : H → ℂ) (hφ : Continuous φ)
    (hφΓ : ∀ γ ∈ Γ, ∀ h, φ (γ * h) = φ h)
    (hbound : ∃ C : ℝ, ∀ h, ‖φ h‖ ≤ C) :
    ((Measure.haar : Measure H) (fundamentalDomain Γ hΓ)).toReal⁻¹ •
        ∫ h in fundamentalDomain Γ hΓ, φ h ∂Measure.haar =
      ((Measure.haar : Measure M) (fundamentalDomain ΓM hΓM)).toReal⁻¹ •
        ∫ m in fundamentalDomain ΓM hΓM,
          ((Measure.haar : Measure N) (fundamentalDomain (Γ.comap i) hΓN)).toReal⁻¹ •
            ∫ n in fundamentalDomain (Γ.comap i) hΓN, φ (i n * j m) ∂Measure.haar
          ∂Measure.haar := by
  classical
  let Φ := prodHomeomorph i j p hpj hker hpi hi hj hp
  let EN := fundamentalDomain (Γ.comap i) hΓN
  let EM := fundamentalDomain ΓM hΓM
  let ν := (Measure.haar : Measure N).prod (Measure.haar : Measure M)
  obtain ⟨c, hc⟩ := exists_haar_eq_smul_map_prod hpj hker hpi hi hj hp
    (mulEquivHaarChar_conj_eq_one_of_finiteCovolume
      i j p hpj hker hpi hi hj Γ ΓM hΓM hjΓ hΓN)
  have hEN : (Measure.haar : Measure N) EN < ∞ :=
    (haar_fundamentalDomain_ne_top (Γ.comap i) hΓN).lt_top
  have hEM : (Measure.haar : Measure M) EM < ∞ :=
    (haar_fundamentalDomain_ne_top ΓM hΓM).lt_top
  have : IsFiniteMeasure ((Measure.haar : Measure N).restrict EN) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hEN⟩
  have : IsFiniteMeasure ((Measure.haar : Measure M).restrict EM) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hEM⟩
  have hI : IntegrableOn (fun x : N × M => φ (Φ x)) (EN ×ˢ EM) ν := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    obtain ⟨C, hC⟩ := hbound
    exact ⟨(hφ.comp Φ.continuous).stronglyMeasurable.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (ae_of_all _ fun x => hC (Φ x))⟩
  have hdomain := isFundamentalDomain_product
    i j p hpj hker hpi hi hj hp Γ ΓM hΓM hjΓ hpΓ hΓN
  have : Countable Γ := countable_of_isDiscrete Γ hΓ
  have hS : MeasurableSet (Φ '' (EN ×ˢ EM)) := by
    rw [Φ.image_eq_preimage_symm]
    exact Φ.symm.continuous.measurable
      ((measurableSet_fundamentalDomain (Γ.comap i) hΓN).prod
        (measurableSet_fundamentalDomain ΓM hΓM))
  -- the period over `Γ \ H`
  have hint : ∫ h in fundamentalDomain Γ hΓ, φ h ∂Measure.haar =
      (c : ℝ) • ∫ m in EM, ∫ n in EN, φ (i n * j m) ∂Measure.haar ∂Measure.haar := by
    rw [(isFundamentalDomain Γ hΓ Measure.haar).setIntegral_eq hdomain
      (fun γ h => hφΓ γ γ.property h)]
    rw [hc, Measure.restrict_smul, integral_smul_nnreal_measure]
    change c • (∫ h in Φ '' (EN ×ˢ EM), φ h ∂ν.map Φ) = _
    rw [Φ.isClosedEmbedding.setIntegral_map, Φ.preimage_image]
    have hFubini :
        ∫ x in EN ×ˢ EM, φ (Φ x) ∂ν =
          ∫ m in EM, ∫ n in EN, φ (i n * j m) ∂Measure.haar ∂Measure.haar := by
      rw [← Measure.prod_restrict]
      rw [IntegrableOn, ← Measure.prod_restrict] at hI
      exact integral_prod_symm _ hI
    rw [hFubini]
    rfl
  -- the mass of `Γ \ H`
  have hmass : (Measure.haar : Measure H) (fundamentalDomain Γ hΓ) =
      (c : ℝ≥0∞) * ((Measure.haar : Measure N) EN * (Measure.haar : Measure M) EM) := by
    rw [(isFundamentalDomain Γ hΓ Measure.haar).measure_eq hdomain, hc,
      Measure.smul_apply, Measure.map_apply Φ.continuous.measurable hS, Φ.preimage_image,
      Measure.prod_prod, ENNReal.smul_def, smul_eq_mul]
  have hH0 := haar_fundamentalDomain_ne_zero Γ hΓ
  have hc0 : (c : ℝ) ≠ 0 := by
    intro h0
    apply hH0
    rw [hmass, show (c : ℝ≥0∞) = 0 by exact_mod_cast (show c = 0 by exact_mod_cast h0),
      zero_mul]
  have hmassR : ((Measure.haar : Measure H) (fundamentalDomain Γ hΓ)).toReal =
      (c : ℝ) * (((Measure.haar : Measure N) EN).toReal *
        ((Measure.haar : Measure M) EM).toReal) := by
    rw [hmass, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]
  have hN0 : ((Measure.haar : Measure N) EN).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨haar_fundamentalDomain_ne_zero _ hΓN, hEN.ne⟩
  have hM0 : ((Measure.haar : Measure M) EM).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨haar_fundamentalDomain_ne_zero _ hΓM, hEM.ne⟩
  rw [hint, hmassR, smul_smul, integral_smul, smul_smul]
  congr 1
  simp only [EN, EM]
  field_simp

end Langlands.Global.LeftCosetSpace.Semidirect

namespace Langlands.Global.LeftCosetSpace.Semidirect

variable {N : Type u} {M : Type v} {H : Type w}
  [Group N] [Group M] [Group H]
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

include hpj hker hpi hi hj hp hΓM hjΓ hpΓ in
/-- Compact quotients version of `normalizedPeriod_eq_iterated`, with a separately named
normal lattice. -/
theorem normalizedPeriod_eq_iterated_of_compact
    (ΓN : Subgroup N) (hΓN : IsDiscrete (ΓN : Set N))
    (hiΓ : ∀ n, i n ∈ Γ ↔ n ∈ ΓN)
    [CompactSpace (Langlands.Global.LeftCosetSpace ΓN)]
    [CompactSpace (Langlands.Global.LeftCosetSpace ΓM)]
    [CompactSpace (Langlands.Global.LeftCosetSpace Γ)]
    (φ : H → ℂ) (hφ : Continuous φ)
    (hφΓ : ∀ γ ∈ Γ, ∀ h, φ (γ * h) = φ h) :
    ((Measure.haar : Measure H) (fundamentalDomain Γ hΓ)).toReal⁻¹ •
        ∫ h in fundamentalDomain Γ hΓ, φ h ∂Measure.haar =
      ((Measure.haar : Measure M) (fundamentalDomain ΓM hΓM)).toReal⁻¹ •
        ∫ m in fundamentalDomain ΓM hΓM,
          ((Measure.haar : Measure N) (fundamentalDomain ΓN hΓN)).toReal⁻¹ •
            ∫ n in fundamentalDomain ΓN hΓN, φ (i n * j m) ∂Measure.haar
          ∂Measure.haar := by
  have := isLocallyFiniteMeasure_haarQuotientMeasure ΓN hΓN
  have := isLocallyFiniteMeasure_haarQuotientMeasure ΓM hΓM
  have heq : Γ.comap i = ΓN := Subgroup.ext hiΓ
  subst ΓN
  let f := lift Γ φ (fun γ h => hφΓ γ γ.property h)
  have hf : Continuous f := continuous_lift Γ _ _ hφ
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact normalizedPeriod_eq_iterated i j p hpj hker hpi hi hj hp Γ hΓ ΓM hΓM hjΓ hpΓ hΓN
    φ hφ hφΓ ⟨C, fun h => hC (mk Γ h) (mem_univ _)⟩

/-- On a unimodular group, a multiplicative function trivial on a discrete subgroup and not
identically one has zero Bochner integral over the chosen fundamental domain (right
translation by a point where it differs from one multiplies the integral by that value). -/
theorem setIntegral_fundamentalDomain_character_eq_zero
    [(Measure.haar : Measure M).IsMulRightInvariant]
    (θ : M → ℂ) (hθmul : ∀ a b, θ (a * b) = θ a * θ b)
    (hθΓ : ∀ γ ∈ ΓM, θ γ = 1) {m₀ : M} (hm₀ : θ m₀ ≠ 1) :
    ∫ m in fundamentalDomain ΓM hΓM, θ m ∂Measure.haar = 0 := by
  have : Countable ΓM := countable_of_isDiscrete ΓM hΓM
  set E := fundamentalDomain ΓM hΓM
  have hE : IsFundamentalDomain ΓM E (Measure.haar : Measure M) := isFundamentalDomain ΓM hΓM _
  have hE' : IsFundamentalDomain ΓM ((· * m₀⁻¹) ⁻¹' E) (Measure.haar : Measure M) :=
    hE.preimage_of_equiv (quasiMeasurePreserving_mul_right _ m₀⁻¹) Function.bijective_id
      (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
  have hinv : ∀ (γ : ΓM) (x : M), θ (γ • x) = θ x := by
    intro γ x
    rw [Subgroup.smul_def, smul_eq_mul, hθmul, hθΓ γ γ.property, one_mul]
  have h1 : ∫ m in (· * m₀⁻¹) ⁻¹' E, θ m ∂Measure.haar = ∫ m in E, θ m ∂Measure.haar :=
    hE'.setIntegral_eq hE hinv
  have h2 : ∫ m in (· * m₀⁻¹) ⁻¹' E, θ m ∂Measure.haar =
      ∫ m in E, θ (m * m₀) ∂Measure.haar := by
    have hmp := measurePreserving_mul_right (Measure.haar : Measure M) m₀⁻¹
    have := hmp.setIntegral_preimage_emb
      (measurableEmbedding_mulRight m₀⁻¹) (fun m => θ (m * m₀)) E
    simpa only [inv_mul_cancel_right] using this
  rw [h1] at h2
  simp_rw [hθmul] at h2
  rw [integral_mul_const] at h2
  have h3 : (∫ m in E, θ m ∂Measure.haar) * (θ m₀ - 1) = 0 := by
    rw [mul_sub, mul_one, ← h2, sub_self]
  rcases mul_eq_zero.mp h3 with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hm₀

end Langlands.Global.LeftCosetSpace.Semidirect
