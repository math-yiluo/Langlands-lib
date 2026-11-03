import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SphericalLevi

/-! # Lemma II.4.3 from Lemma II.4.2

Waldspurger 2003, Lemma II.4.3: for some `d` the integral
`∫_Ū δ_P(m_P(ū))^{1/2} Ξ^M(m_P(ū)) (1 + σ(ū))^{-d} dū` converges. The proof averages the
integral of Lemma II.4.2 over conjugation by `K ∩ M` and identifies the inner integral with
`δ_P(m_P(ū))^{1/2} Ξ^M(m_P(ū))` (Lemma II.1.6 pointwise). Here the data are those of
`SphericalLevi` (`LeviData`), and `U` is a subgroup normalized by `M` with a measure `ν`
satisfying the modulus relation `IsConjModulus` for a character trivial on `K ∩ M`.
-/

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory Filter

namespace Langlands.HarishChandraSchwartz

universe u

section Levi

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] {K P₀ P M U : Subgroup G}
  {δ₀ : P₀ →* ℝ≥0ˣ} {δP : M →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ} {mP : P →* M}
  [CompactSpace (K.subgroupOf M)]
  {hMU : M ≤ Subgroup.normalizer (U : Set G)} {ν : Measure U} {δ : M →* ℝ≥0ˣ}

/-- The weight `g ↦ δ_P(m_P(g))^{1/2} Ξ^M(m_P(g))` of Lemmas II.1.6 and II.4.3, where
`m_P(g)` is the Levi component (`leviComponent`) of the factorization `g = p k` and
`Ξ^M = xi hM δ₀M` is the spherical function of `M`. -/
def leviXiWeight (hPK : IsIwasawaPair P K) (mP : P →* M) (δP : M →* ℝ≥0ˣ)
    (hM : IsIwasawaPair (P₀.subgroupOf M) (K.subgroupOf M)) (δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ)
    (g : G) : ℝ :=
  NNReal.sqrt (δP (leviComponent hPK mP g) : ℝ≥0) * xi hM δ₀M (leviComponent hPK mP g)

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [CompactSpace (K.subgroupOf M)] in
/-- The pointwise identity behind Lemma II.4.3: for `k ∈ K ∩ M` and `u ∈ G`,
`φ₀(k u k⁻¹) = δ_P(m_P(u))^{1/2} φ₀^M(k m_P(u))`, where `φ₀(p k) = δ₀(p)^{1/2}` and `φ₀^M`
is the analogous weight of `M`. -/
theorem LeviData.iwasawaWeight_conj (hL : LeviData K P₀ P M δ₀ δP δ₀M mP)
    (hP₀K : IsIwasawaPair P₀ K) (hM : IsIwasawaPair (P₀.subgroupOf M) (K.subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1) (kM : K.subgroupOf M) (u : G) :
    iwasawaWeight hP₀K δ₀ (((kM : M) : G) * u * ((kM : M) : G)⁻¹) =
      NNReal.sqrt (δP (leviComponent (hP₀K.mono hL.le_P₀) mP u) : ℝ≥0) *
        iwasawaWeight hM δ₀M ((kM : M) * leviComponent (hP₀K.mono hL.le_P₀) mP u) := by
  have hk : ((kM : M) : G) ∈ K := kM.2
  rw [iwasawaWeight_mul_right (hPK := hP₀K) hδ₀ _ (K.inv_mem hk)]
  obtain ⟨k', hk', hfac⟩ := exists_iwasawaFactor (hP₀K.mono hL.le_P₀) u
  set p := iwasawaFactor (hP₀K.mono hL.le_P₀) u
  conv_lhs => rw [hfac, ← mul_assoc, iwasawaWeight_mul_right (hPK := hP₀K) hδ₀ _ hk']
  exact hL.iwasawaWeight_mul hP₀K hM hδ₀ p kM

variable [SecondCountableTopology U] [SFinite ν]

/-- Waldspurger, Lemma II.4.3, from Lemma II.4.2: if
`∫_U φ₀(u) (1 + σ(u))^{-d} dν(u) < ∞` for some `d` (`UnipotentWeightIntegrable`), then the
same holds for the weight `u ↦ δ_P(m_P(u))^{1/2} Ξ^M(m_P(u))`, where `Ξ^M = xi hM δ₀M`.
The hypotheses: the Levi data, `K` open, `δ₀` trivial on `P₀ ∩ K` (`hδ₀`), the
modulus relation for `ν` with a character trivial on `K ∩ M`, and `σ` measurable,
nonnegative and invariant under conjugation by `K ∩ M`. -/
theorem LeviData.unipotentWeightIntegrable (hL : LeviData K P₀ P M δ₀ δP δ₀M mP)
    (hK : IsOpen (K : Set G)) (hP₀K : IsIwasawaPair P₀ K)
    (hM : IsIwasawaPair (P₀.subgroupOf M) (K.subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hν : IsConjModulus hMU ν δ) (hδK : ∀ k : M, (k : G) ∈ K → δ k = 1)
    {σ : G → ℝ} (hσm : Measurable σ) (hσ : ∀ g, 0 ≤ σ g)
    (hσK : ∀ k : M, (k : G) ∈ K → ∀ g, σ ((k : G) * g * (k : G)⁻¹) = σ g)
    (h42 : UnipotentWeightIntegrable ν (fun u : U => iwasawaWeight hP₀K δ₀ u) σ) :
    UnipotentWeightIntegrable ν
      (fun u : U => leviXiWeight (hP₀K.mono hL.le_P₀) mP δP hM δ₀M u) σ := by
  simp only [leviXiWeight]
  obtain ⟨d, hI⟩ := h42
  refine ⟨d, ?_⟩
  set KM := K.subgroupOf M
  set νK := normalizedHaar KM
  set hPK := hP₀K.mono hL.le_P₀
  have hpos : ∀ g, 0 < 1 + σ g := fun g => by linarith [hσ g]
  set F : U → ℝ≥0∞ := fun u =>
    ENNReal.ofReal (iwasawaWeight hP₀K δ₀ u * (1 + σ u) ^ (-d)) with hF
  -- conjugation by `k ∈ K ∩ M` does not change the integral
  have hconj : ∀ k : KM, ∫⁻ u, F u ∂ν = ∫⁻ u,
      ENNReal.ofReal (iwasawaWeight hP₀K δ₀ (((k : M) : G) * u * ((k : M) : G)⁻¹)) *
        ENNReal.ofReal ((1 + σ u) ^ (-d)) ∂ν := by
    intro k
    have hk : ((k : M) : G) ∈ K := k.2
    have h := hν.lintegral_comp (k : M) F
    rw [hδK _ hk] at h
    simp only [Units.val_one, inv_one, ENNReal.coe_one, one_mul] at h
    rw [← h]
    refine lintegral_congr fun u => ?_
    simp only [hF, conjUnipotent, hσK _ hk]
    rw [ENNReal.ofReal_mul (iwasawaWeight_nonneg _)]
  have havg : ∫⁻ u, F u ∂ν = ∫⁻ k : KM, ∫⁻ u,
      ENNReal.ofReal (iwasawaWeight hP₀K δ₀ (((k : M) : G) * u * ((k : M) : G)⁻¹)) *
        ENNReal.ofReal ((1 + σ u) ^ (-d)) ∂ν ∂νK := by
    simp_rw [← hconj]
    rw [lintegral_const, measure_univ, mul_one]
  have hφc : Continuous (iwasawaWeight hP₀K δ₀) := continuous_iwasawaWeight hδ₀ hK
  have hmeas : AEMeasurable (Function.uncurry fun (k : KM) (u : U) =>
      ENNReal.ofReal (iwasawaWeight hP₀K δ₀ (((k : M) : G) * u * ((k : M) : G)⁻¹)) *
        ENNReal.ofReal ((1 + σ u) ^ (-d))) (νK.prod ν) := by
    refine Measurable.aemeasurable ?_
    show Measurable fun p : KM × U =>
      ENNReal.ofReal (iwasawaWeight hP₀K δ₀ (((p.1 : M) : G) * p.2 * ((p.1 : M) : G)⁻¹)) *
        ENNReal.ofReal ((1 + σ p.2) ^ (-d))
    have hc : Continuous fun p : KM × U => ((p.1 : M) : G) * p.2 * ((p.1 : M) : G)⁻¹ := by
      have h1 : Continuous fun p : KM × U => ((p.1 : M) : G) :=
        continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)
      exact (h1.mul (continuous_subtype_val.comp continuous_snd)).mul h1.inv
    refine Measurable.mul (ENNReal.measurable_ofReal.comp (hφc.comp hc).measurable) ?_
    refine ENNReal.measurable_ofReal.comp ?_
    exact ((measurable_const.add (hσm.comp (measurable_subtype_coe.comp measurable_snd))).pow_const
      _)
  rw [havg, lintegral_lintegral_swap hmeas] at hI
  -- the inner integral over `K ∩ M` is `δ_P(m_P(u))^{1/2} Ξ^M(m_P(u))`
  have hinner : ∀ u : U, ∫⁻ k : KM,
      ENNReal.ofReal (iwasawaWeight hP₀K δ₀ (((k : M) : G) * u * ((k : M) : G)⁻¹)) *
        ENNReal.ofReal ((1 + σ u) ^ (-d)) ∂νK =
      ENNReal.ofReal (NNReal.sqrt (δP (leviComponent hPK mP u) : ℝ≥0) *
        xi hM δ₀M (leviComponent hPK mP u) * (1 + σ u) ^ (-d)) := by
    intro u
    have hc : Continuous fun k : KM =>
        iwasawaWeight hP₀K δ₀ (((k : M) : G) * u * ((k : M) : G)⁻¹) := by
      have h1 : Continuous fun k : KM => ((k : M) : G) :=
        continuous_subtype_val.comp continuous_subtype_val
      exact hφc.comp ((h1.mul continuous_const).mul h1.inv)
    have hint : Integrable (fun k : KM =>
        iwasawaWeight hP₀K δ₀ (((k : M) : G) * u * ((k : M) : G)⁻¹)) νK :=
      hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [lintegral_mul_const _ hc.measurable.ennreal_ofReal,
      ← ofReal_integral_eq_lintegral_ofReal hint
        (Eventually.of_forall fun k => iwasawaWeight_nonneg _),
      ← ENNReal.ofReal_mul (integral_nonneg fun k => iwasawaWeight_nonneg _)]
    congr 1
    congr 1
    simp_rw [hL.iwasawaWeight_conj hP₀K hM hδ₀]
    rw [integral_const_mul]
    rfl
  simp_rw [hinner] at hI
  exact hI

end Levi

end Langlands.HarishChandraSchwartz
