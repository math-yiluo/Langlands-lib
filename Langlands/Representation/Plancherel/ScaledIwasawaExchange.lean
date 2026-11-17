import Langlands.Representation.Plancherel.NormalizedIwasawaPush

/-! # Opposite Iwasawa integration up to a positive factor -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace Langlands.Plancherel.LeviInvariantIwasawaExchange

open Aubert.General

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {P M U P' V : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (h' : IsSemidirectDecomposition P' M V)
  (K : OpenSubgroup G)
  [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace U] [BorelSpace U] [SecondCountableTopology U]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (μM : Measure M) (μU : Measure U) (μV : Measure V)

/-- The exact relative compact-coordinate mass of the two Iwasawa measures. -/
def iwasawaExchangeRatio : ℝ≥0∞ :=
  iwasawaCompactMass K μM μV * (iwasawaCompactMass K μM μU)⁻¹

variable [μM.IsHaarMeasure] [μU.IsHaarMeasure] [μV.IsHaarMeasure]
  [SFinite μM] [SFinite μU] [SFinite μV]

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [BorelSpace M] [BorelSpace U] [SecondCountableTopology U]
  [BorelSpace V] [SecondCountableTopology V] [SFinite μM] in
/-- The ratio is nonzero for the actual closed-parabolic compact data. -/
theorem iwasawaExchangeRatio_ne_zero
    (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
    (hr : Continuous h.projection) : iwasawaExchangeRatio K μM μU μV ≠ 0 :=
  mul_ne_zero (iwasawaCompactMass_ne_zero K μM μV)
    (ENNReal.inv_ne_zero.mpr (iwasawaCompactMass_ne_top h K μM μU hP hK hr))

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [BorelSpace M] [BorelSpace U] [SecondCountableTopology U]
  [BorelSpace V] [SecondCountableTopology V] [SFinite μM] in
/-- The ratio is finite for the actual closed-parabolic compact data. -/
theorem iwasawaExchangeRatio_ne_top
    (hP' : IsClosed (P' : Set G)) (hK : IsCompact (K : Set G))
    (hr' : Continuous h'.projection) : iwasawaExchangeRatio K μM μU μV ≠ ⊤ :=
  ENNReal.mul_ne_top (iwasawaCompactMass_ne_top h' K μM μV hP' hK hr')
    (ENNReal.inv_ne_top.mpr (iwasawaCompactMass_ne_zero K μM μU))

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [BorelSpace M] [BorelSpace U] [SecondCountableTopology U]
  [BorelSpace V] [SecondCountableTopology V] [SFinite μM] in
/-- The real comparison factor is strictly positive. -/
theorem iwasawaExchangeRatio_toReal_pos
    (hP : IsClosed (P : Set G)) (hP' : IsClosed (P' : Set G))
    (hK : IsCompact (K : Set G))
    (hr : Continuous h.projection) (hr' : Continuous h'.projection) :
    0 < (iwasawaExchangeRatio K μM μU μV).toReal :=
  ENNReal.toReal_pos (iwasawaExchangeRatio_ne_zero h K μM μU μV hP hK hr)
    (iwasawaExchangeRatio_ne_top h' K μM μU μV hP' hK hr')

variable {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant] [μM.IsMulRightInvariant]

/-- The original, unnormalized quotient pushforwards are positively
proportional for arbitrary compact Iwasawa data. -/
theorem iwasawaPush_eq_ratio_smul
    (hP : IsClosed (P : Set G)) (hP' : IsClosed (P' : Set G))
    (hK : IsCompact (K : Set G))
    (hr : Continuous h.projection) (hr' : Continuous h'.projection)
    (hfac : ∀ g : G, ∃ m : M, ∃ u : U, ∃ k ∈ K, g = (m : G) * u * k)
    (hfac' : ∀ g : G, ∃ m : M, ∃ v : V, ∃ k ∈ K, g = (m : G) * v * k) :
    iwasawaPush M μ K μV = iwasawaExchangeRatio K μM μU μV • iwasawaPush M μ K μU := by
  have he := normalizedIwasawaPush_eq (μ := μ) h K μM μU h' μV
    hP hP' hK hr hr' hfac hfac'
  calc
    _ = iwasawaCompactMass K μM μV • normalizedIwasawaPush (μ := μ) K μM μV := by
      rw [normalizedIwasawaPush, smul_smul,
        ENNReal.mul_inv_cancel (iwasawaCompactMass_ne_zero K μM μV)
          (iwasawaCompactMass_ne_top h' K μM μV hP' hK hr'), one_smul]
    _ = iwasawaCompactMass K μM μV • normalizedIwasawaPush (μ := μ) K μM μU := by rw [he]
    _ = _ := by rw [normalizedIwasawaPush, smul_smul]; rfl

/-- Absolute integrability transfers between the two Iwasawa coordinates.
Their complex integrals differ by the explicit positive real comparison
factor, without any compact splitting. -/
theorem integral_exchange_scaled
    (hP : IsClosed (P : Set G)) (hP' : IsClosed (P' : Set G))
    (hK : IsCompact (K : Set G))
    (hr : Continuous h.projection) (hr' : Continuous h'.projection)
    (hfac : ∀ g : G, ∃ m : M, ∃ u : U, ∃ k ∈ K, g = (m : G) * u * k)
    (hfac' : ∀ g : G, ∃ m : M, ∃ v : V, ∃ k ∈ K, g = (m : G) * v * k)
    (Θ : G → ℂ) (hΘ : Measurable Θ)
    (hinv : ∀ (m : M) (g : G), Θ ((m : G) * g) = Θ g)
    (hint : Integrable (fun p : G × V => Θ ((p.2 : G) * p.1))
      ((μ.restrict (K : Set G)).prod μV)) :
    Integrable (fun p : G × U => Θ ((p.2 : G) * p.1))
        ((μ.restrict (K : Set G)).prod μU) ∧
      (∫ k in (K : Set G), ∫ v, Θ ((v : G) * k) ∂μV ∂μ) =
        (iwasawaExchangeRatio K μM μU μV).toReal •
          (∫ k in (K : Set G), ∫ u, Θ ((u : G) * k) ∂μU ∂μ) := by
  have hpush := iwasawaPush_eq_ratio_smul (μ := μ) h h' K μM μU μV
    hP hP' hK hr hr' hfac hfac'
  have hV := measurable_iwasawaCoordinates (M := M) (W := V)
  have hU := measurable_iwasawaCoordinates (M := M) (W := U)
  have hL := measurable_leviQuotientLift M Θ hΘ hinv
  have hintV : Integrable (leviQuotientLift M Θ hinv) (iwasawaPush M μ K μV) :=
    (integrable_map_measure hL.aestronglyMeasurable hV.aemeasurable).mpr hint
  rw [hpush] at hintV
  have hintL := (integrable_smul_measure
    (iwasawaExchangeRatio_ne_zero h K μM μU μV hP hK hr)
    (iwasawaExchangeRatio_ne_top h' K μM μU μV hP' hK hr')).mp hintV
  have hintU : Integrable (fun p : G × U => Θ ((p.2 : G) * p.1))
      ((μ.restrict (K : Set G)).prod μU) :=
    (integrable_map_measure hL.aestronglyMeasurable hU.aemeasurable).mp hintL
  refine ⟨hintU, ?_⟩
  rw [← integral_prod _ hint, ← integral_prod _ hintU]
  have h1 := integral_map (μ := (μ.restrict (K : Set G)).prod μV)
    hV.aemeasurable hL.aestronglyMeasurable
  have h2 := integral_map (μ := (μ.restrict (K : Set G)).prod μU)
    hU.aemeasurable hL.aestronglyMeasurable
  change ∫ q, leviQuotientLift M Θ hinv q ∂iwasawaPush M μ K μV = _ at h1
  change ∫ q, leviQuotientLift M Θ hinv q ∂iwasawaPush M μ K μU = _ at h2
  calc
    _ = ∫ q, leviQuotientLift M Θ hinv q ∂iwasawaPush M μ K μV := h1.symm
    _ = (iwasawaExchangeRatio K μM μU μV).toReal •
        ∫ q, leviQuotientLift M Θ hinv q ∂iwasawaPush M μ K μU := by
      rw [hpush, integral_smul_measure]
    _ = _ := congrArg (fun z : ℂ => (iwasawaExchangeRatio K μM μU μV).toReal • z) h2

end Langlands.Plancherel.LeviInvariantIwasawaExchange
