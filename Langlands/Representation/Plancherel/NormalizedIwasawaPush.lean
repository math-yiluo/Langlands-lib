import Langlands.Representation.Plancherel.NormalizedIwasawaCutoff

/-! # Normalized opposite Iwasawa measures without compact splitting -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace Langlands.Plancherel.LeviInvariantIwasawaExchange

open Aubert.General HarishChandraSchwartz Induction

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (K : OpenSubgroup G)
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U]
  (μM : Measure M) (μU : Measure U)

/-- The mass of `P ∩ K` in actual Levi-then-radical product coordinates. -/
def iwasawaCompactMass : ℝ≥0∞ :=
  (μM.prod μU) (leviUnipotentMul ⁻¹' (K : Set G))

variable [μM.IsHaarMeasure] [μU.IsHaarMeasure] [SFinite μM] [SFinite μU]

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [BorelSpace M] [BorelSpace U] [SecondCountableTopology U] [SFinite μM] in
/-- The compact-coordinate mass is positive. -/
theorem iwasawaCompactMass_ne_zero : iwasawaCompactMass K μM μU ≠ 0 := by
  exact (continuous_leviUnipotentMul.isOpen_preimage _ K.isOpen).measure_ne_zero
    (μM.prod μU) ⟨(1, 1), by simp [leviUnipotentMul]⟩

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace U] [BorelSpace U]
  [SecondCountableTopology U] in
/-- The coordinate preimage of `K` is compact. -/
theorem isCompact_iwasawaCompactPreimage (hP : IsClosed (P : Set G))
    (hK : IsCompact (K : Set G)) (hr : Continuous h.projection) :
    IsCompact (leviUnipotentMul (M := M) (U := U) ⁻¹' (K : Set G)) := by
  have hc := (isCompact_conjOpenSubgroup P hP K hK 1).image
    (h.coordinates hr).symm.continuous
  convert hc using 1
  ext x
  constructor
  · intro hx
    refine ⟨h.coordinates hr x, ?_, (h.coordinates hr).symm_apply_apply x⟩
    apply Induction.mem_conjOpenSubgroup.mpr
    change (x.1 : G) * (x.2 : G) ∈ K at hx
    change (1 : G)⁻¹ * ((x.1 : G) * (x.2 : G)) * 1 ∈ K
    simpa only [inv_one, one_mul, mul_one] using hx
  · rintro ⟨p, hp, rfl⟩
    have hp' : (p : G) ∈ K := by
      have hp' := Induction.mem_conjOpenSubgroup.mp hp
      simpa only [inv_one, one_mul, mul_one] using hp' 
    have he := congrArg (fun q : P => (q : G)) ((h.coordinates hr).apply_symm_apply p)
    change leviUnipotentMul ((h.coordinates hr).symm p) ∈ K
    change leviUnipotentMul ((h.coordinates hr).symm p) = (p : G) at he
    rw [he]
    exact hp'

omit [SFinite μM] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [BorelSpace M] [BorelSpace U] [SecondCountableTopology U] in
/-- The compact-coordinate mass is finite. -/
theorem iwasawaCompactMass_ne_top (hP : IsClosed (P : Set G))
    (hK : IsCompact (K : Set G)) (hr : Continuous h.projection) :
    iwasawaCompactMass K μM μU ≠ ⊤ :=
  (isCompact_iwasawaCompactPreimage h K hP hK hr).measure_ne_top

variable {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant]

include h in
/-- The factorization formula retains the exact compact-coordinate mass and
therefore needs no compact splitting. -/
theorem lintegral_iwasawa_eq_mass
    (hfac : ∀ g : G, ∃ m : M, ∃ u : U, ∃ k ∈ K, g = (m : G) * u * k)
    (F : G → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ k in (K : Set G), ∫⁻ m, ∫⁻ u, F ((m : G) * u * k) ∂μU ∂μM ∂μ =
      iwasawaCompactMass K μM μU * ∫⁻ g, F g ∂μ := by
  have hι : Measurable (leviUnipotentMul (M := M) (U := U)) :=
    continuous_leviUnipotentMul.measurable
  have hb := CompactFactorization.lintegral_restrict_lintegral_mul μ K
    K.isOpen.measurableSet (μM.prod μU) leviUnipotentMul hι
    (fun g => by
      obtain ⟨m, u, k, hk, rfl⟩ := hfac g
      exact ⟨(m, u), k, hk, rfl⟩)
    (fun x₀ => ⟨leviUnipotentShift h.levi_le_normalizer x₀,
      measurePreserving_shift h.levi_le_normalizer x₀,
      fun x => leviUnipotentMul_shift h.levi_le_normalizer x₀ x⟩) F hF
  calc
    _ = ∫⁻ k in (K : Set G), ∫⁻ x : M × U, F (leviUnipotentMul x * k) ∂μM.prod μU ∂μ := by
      refine lintegral_congr fun k => ?_
      exact (lintegral_prod _ (hF.comp (hι.mul_const k)).aemeasurable).symm
    _ = _ := hb

/-- Integrating a left-Levi-invariant function in Iwasawa coordinates is its
normalized-cutoff integral times the exact positive compact-coordinate mass. -/
theorem lintegral_iwasawa_eq_normalizedCutoff
    (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
    (hr : Continuous h.projection)
    (hfac : ∀ g : G, ∃ m : M, ∃ u : U, ∃ k ∈ K, g = (m : G) * u * k)
    (Θ : G → ℝ≥0∞) (hΘ : Measurable Θ)
    (hinv : ∀ (m : M) (g : G), Θ ((m : G) * g) = Θ g) :
    ∫⁻ k in (K : Set G), ∫⁻ u, Θ ((u : G) * k) ∂μU ∂μ =
      iwasawaCompactMass K μM μU *
        ∫⁻ g, normalizedIwasawaCutoff h K μM g * Θ g ∂μ := by
  rw [← lintegral_iwasawa_eq_mass h K μM μU hfac
    (fun g => normalizedIwasawaCutoff h K μM g * Θ g)
    ((measurable_normalizedIwasawaCutoff h K μM).mul hΘ)]
  apply setLIntegral_congr_fun K.isOpen.measurableSet
  intro k hk
  let a := μM (projectedCompactOpenSubgroup h K : Set M)
  let S := ∫⁻ u : U, Θ ((u : G) * k) ∂μU
  have hmeasU : Measurable fun u : U => Θ ((u : G) * k) :=
    hΘ.comp (continuous_subtype_val.measurable.mul_const k)
  have hinner : ∀ m : M,
      ∫⁻ u, normalizedIwasawaCutoff h K μM ((m : G) * u * k) *
        Θ ((m : G) * u * k) ∂μU =
      a⁻¹ * (projectedCompactOpenSubgroup h K : Set M).indicator 1 m * S := by
    intro m
    simp_rw [normalizedIwasawaCutoff, cutoff_mul_projected h K m _ hk,
      mul_assoc (m : G), hinv]
    exact lintegral_const_mul _ (f := fun u : U => Θ ((u : G) * k)) hmeasU
  simp_rw [hinner]
  rw [lintegral_mul_const S
      (f := fun m : M => a⁻¹ * (projectedCompactOpenSubgroup h K : Set M).indicator 1 m)
      (measurable_const.mul
        (measurable_one.indicator (projectedCompactOpenSubgroup h K).isOpen.measurableSet)),
    lintegral_const_mul a⁻¹
      (f := (projectedCompactOpenSubgroup h K : Set M).indicator 1)
      (measurable_one.indicator (projectedCompactOpenSubgroup h K).isOpen.measurableSet),
    lintegral_indicator_one (projectedCompactOpenSubgroup h K).isOpen.measurableSet,
    ENNReal.inv_mul_cancel (projectedCompact_mass_ne_zero h K μM)
      (projectedCompact_mass_ne_top h K μM hP hK hr), one_mul]

/-- The actual Iwasawa pushforward divided by its compact-coordinate mass. -/
def normalizedIwasawaPush : Measure (LeviQuotient M) :=
  (iwasawaCompactMass K μM μU)⁻¹ • iwasawaPush M μ K μU

/-- The normalized pushforward is precisely the normalized-cutoff quotient
measure, evaluated on every nonnegative measurable quotient function. -/
theorem lintegral_normalizedIwasawaPush
    (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
    (hr : Continuous h.projection)
    (hfac : ∀ g : G, ∃ m : M, ∃ u : U, ∃ k ∈ K, g = (m : G) * u * k)
    (f : LeviQuotient M → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ q, f q ∂normalizedIwasawaPush (μ := μ) K μM μU =
      ∫⁻ g, normalizedIwasawaCutoff h K μM g * f (leviQuotientMk M g) ∂μ := by
  have hi := measurable_iwasawaCoordinates (M := M) (W := U)
  rw [normalizedIwasawaPush, lintegral_smul_measure, smul_eq_mul,
    iwasawaPush, lintegral_map hf hi,
    lintegral_prod (fun p : G × U => f (leviQuotientMk M ((p.2 : G) * p.1)))
      (hf.comp hi).aemeasurable]
  change (iwasawaCompactMass K μM μU)⁻¹ *
    (∫⁻ k in (K : Set G), ∫⁻ u : U, f (leviQuotientMk M ((u : G) * k)) ∂μU ∂μ) = _
  rw [lintegral_iwasawa_eq_normalizedCutoff h K μM μU hP hK hr hfac
      (fun g => f (leviQuotientMk M g))
      (hf.comp (measurable_leviQuotientMk M))
      (fun m g => by rw [leviQuotientMk_mul]),
    ← mul_assoc, ENNReal.inv_mul_cancel (iwasawaCompactMass_ne_zero K μM μU)
      (iwasawaCompactMass_ne_top h K μM μU hP hK hr), one_mul]

variable {P' V : Subgroup G} (h' : IsSemidirectDecomposition P' M V)
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (μV : Measure V) [μV.IsHaarMeasure] [SFinite μV] [μM.IsMulRightInvariant]

/-- Opposite Iwasawa pushforwards agree after division by their positive finite
compact-coordinate masses. No compact splitting is required. -/
theorem normalizedIwasawaPush_eq
    (hP : IsClosed (P : Set G)) (hP' : IsClosed (P' : Set G))
    (hK : IsCompact (K : Set G))
    (hr : Continuous h.projection) (hr' : Continuous h'.projection)
    (hfac : ∀ g : G, ∃ m : M, ∃ u : U, ∃ k ∈ K, g = (m : G) * u * k)
    (hfac' : ∀ g : G, ∃ m : M, ∃ v : V, ∃ k ∈ K, g = (m : G) * v * k) :
    normalizedIwasawaPush (μ := μ) K μM μV =
      normalizedIwasawaPush (μ := μ) K μM μU := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  calc
    _ = ∫⁻ g, normalizedIwasawaCutoff h' K μM g * f (leviQuotientMk M g) ∂μ :=
      lintegral_normalizedIwasawaPush h' K μM μV hP' hK hr' hfac' f hf
    _ = ∫⁻ g, normalizedIwasawaCutoff h K μM g * f (leviQuotientMk M g) ∂μ :=
      lintegral_normalizedIwasawaCutoff_exchange h K μM h' hP hP' hK hr hr' hfac hfac'
        (fun g => f (leviQuotientMk M g)) (hf.comp (measurable_leviQuotientMk M))
        (fun m g => by rw [leviQuotientMk_mul])
    _ = _ := (lintegral_normalizedIwasawaPush h K μM μU hP hK hr hfac f hf).symm

end Langlands.Plancherel.LeviInvariantIwasawaExchange
