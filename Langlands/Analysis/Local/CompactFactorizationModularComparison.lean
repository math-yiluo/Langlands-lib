import Langlands.Analysis.Local.CompactFactorizationHaar
import Mathlib.MeasureTheory.Group.ModularCharacter

/-!
# Comparing two compact factors through modular-equivariant functions

Let `ι : P → G` be a closed embedding of second countable locally compact groups and let
`K₁`, `K₂` be compact subgroups of `G` with `G = ι(P) K₁ = ι(P) K₂`. A function `φ ≥ 0` on `G`
with `φ(ι(q) g) = Δ_P(q) φ(g)`, where `Δ_P` is the modular character of `P`, has integrals over
`K₁` and `K₂` (for Haar measures) in a fixed ratio, independent of `φ`.
-/

noncomputable section

namespace Langlands.CompactFactorization

open MeasureTheory MeasureTheory.Measure Set Topology Filter
open scoped NNReal ENNReal Pointwise

universe u v

set_option linter.unusedSectionVars false

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {P : Type v} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [T2Space P]
  [LocallyCompactSpace P] [SecondCountableTopology P] [MeasurableSpace P] [BorelSpace P]

/-- **Haar measure on `G = ι(P) K`.** For a closed embedding `ι : P → G` and a compact subgroup
`K` with `G = ι(P) K`, a left Haar measure on `G` is a positive multiple of the pushforward of
`μP × μK` under `(q, k) ↦ ι(q) k`. -/
theorem exists_pos_eq_smul_map_hom_mul_prod (μ : Measure G) [IsHaarMeasure μ]
    (ι : P →* G) (hι : IsClosedEmbedding ι) (K : Subgroup G) (hK : IsCompact (K : Set G))
    (hPK : ∀ g : G, ∃ q : P, ∃ k ∈ K, ι q * k = g)
    (μP : Measure P) [IsHaarMeasure μP] (μK : Measure K) [IsHaarMeasure μK] :
    ∃ c : ℝ≥0, 0 < c ∧
      μ = c • Measure.map (fun p : P × K => ι p.1 * (p.2 : G)) (μP.prod μK) := by
  let Q : Subgroup G := ι.range
  have hQrange : (Q : Set G) = Set.range ι := MonoidHom.coe_range ι
  have hQ : IsClosed (Q : Set G) := by
    rw [hQrange]
    exact hι.isClosed_range
  have : LocallyCompactSpace Q := hQ.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : BorelSpace Q := inferInstanceAs (BorelSpace (Q : Set G))
  have : SecondCountableTopology Q := inferInstanceAs (SecondCountableTopology (Q : Set G))
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : BorelSpace K := inferInstanceAs (BorelSpace (K : Set G))
  let ι' : P →* Q := ι.rangeRestrict
  have hι'c : Continuous ι' := continuous_induced_rng.mpr hι.continuous
  have hι's : Function.Surjective ι' := MonoidHom.rangeRestrict_surjective ι
  have hι'e : IsClosedEmbedding ι' := by
    have h1 : IsEmbedding ι' := by
      have h0 : IsEmbedding (fun q => ((ι' q : Q) : G)) := hι.isEmbedding
      exact (IsEmbedding.subtypeVal.of_comp_iff).mp h0
    exact ⟨h1, by rw [hι's.range_eq]; exact isClosed_univ⟩
  have : (Measure.map ι' μP).IsHaarMeasure :=
    Measure.isHaarMeasure_map μP ι' hι'c hι's hι'e.tendsto_cocompact
  have hQK : ∀ g : G, ∃ q ∈ Q, ∃ k ∈ K, g = q * k := by
    intro g
    obtain ⟨q, k, hk, hg⟩ := hPK g
    exact ⟨ι q, ⟨q, rfl⟩, k, hk, hg.symm⟩
  obtain ⟨c, hc, hμ⟩ := exists_pos_eq_smul_map_mul_prod μ Q hQ K hK hQK (Measure.map ι' μP) μK
  refine ⟨c, hc, ?_⟩
  rw [hμ]
  congr 1
  have hprod : (Measure.map ι' μP).prod μK = Measure.map (Prod.map ι' id) (μP.prod μK) := by
    rw [← Measure.map_prod_map _ _ hι'c.measurable measurable_id, Measure.map_id]
  have hm : Measurable (fun p : Q × K => (p.1 : G) * (p.2 : G)) :=
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).measurable
  rw [hprod, Measure.map_map hm (hι'c.measurable.prodMap measurable_id)]
  rfl

/-- **Comparison of two compact factors.** Let `ι : P → G` be a closed embedding and `K₁`, `K₂`
compact subgroups of `G` with `G = ι(P) K₁ = ι(P) K₂`, with Haar measures `μ₁`, `μ₂`. There is a
constant `c > 0` such that every measurable `φ : G → [0, ∞]` with
`φ(ι(q) g) = Δ_P(q) φ(g)` (`Δ_P` the modular character of `P`) satisfies
`∫_{K₁} φ dμ₁ = c ∫_{K₂} φ dμ₂`. -/
theorem exists_lintegral_compact_eq_of_modular (ι : P →* G) (hι : IsClosedEmbedding ι)
    (K₁ K₂ : Subgroup G) (hK₁ : IsCompact (K₁ : Set G)) (hK₂ : IsCompact (K₂ : Set G))
    (h₁ : ∀ g : G, ∃ q : P, ∃ k ∈ K₁, ι q * k = g)
    (h₂ : ∀ g : G, ∃ q : P, ∃ k ∈ K₂, ι q * k = g)
    (μ₁ : Measure K₁) [IsHaarMeasure μ₁] (μ₂ : Measure K₂) [IsHaarMeasure μ₂] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ φ : G → ℝ≥0∞, Measurable φ →
      (∀ (q : P) (g : G), φ (ι q * g) = (Measure.modularCharacter q : ℝ≥0∞) * φ g) →
      ∫⁻ k, φ k ∂μ₁ = c * ∫⁻ k, φ k ∂μ₂ := by
  have : BorelSpace K₁ := inferInstanceAs (BorelSpace (K₁ : Set G))
  have : BorelSpace K₂ := inferInstanceAs (BorelSpace (K₂ : Set G))
  have : SecondCountableTopology K₁ := inferInstanceAs (SecondCountableTopology (K₁ : Set G))
  have : SecondCountableTopology K₂ := inferInstanceAs (SecondCountableTopology (K₂ : Set G))
  have : CompactSpace K₁ := isCompact_iff_compactSpace.mp hK₁
  have : CompactSpace K₂ := isCompact_iff_compactSpace.mp hK₂
  let μP : Measure P := Measure.haar
  let μ : Measure G := Measure.haar
  have hιc : Continuous ι := hι.continuous
  obtain ⟨c₁, hc₁, hμ₁⟩ := exists_pos_eq_smul_map_hom_mul_prod μ ι hι K₁ hK₁ h₁ μP μ₁
  obtain ⟨c₂, hc₂, hμ₂⟩ := exists_pos_eq_smul_map_hom_mul_prod μ ι hι K₂ hK₂ h₂ μP μ₂
  -- integration over `G` in the coordinates `ι(q) k`
  have hint : ∀ (K : Subgroup G) [BorelSpace K] [SecondCountableTopology K]
      (μK : Measure K) [SFinite μK] (c : ℝ≥0),
      μ = c • Measure.map (fun p : P × K => ι p.1 * (p.2 : G)) (μP.prod μK) →
      ∀ f : G → ℝ≥0∞, Measurable f →
        ∫⁻ g, f g ∂μ = c * ∫⁻ k, ∫⁻ q, f (ι q * (k : G)) ∂μP ∂μK := by
    intro K _ _ μK _ c hμ f hf
    have hm : Measurable (fun p : P × K => ι p.1 * (p.2 : G)) :=
      ((hιc.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).measurable
    rw [hμ, lintegral_smul_measure, lintegral_map hf hm,
      lintegral_prod_symm (fun a : P × K => f (ι a.1 * (a.2 : G))) (hf.comp hm).aemeasurable,
      ENNReal.smul_def, smul_eq_mul]
  refine ⟨c₂ / c₁, div_pos hc₂ hc₁, fun φ hφ hequiv => ?_⟩
  -- the test set `B = W K₁` and the slice mass `b`
  obtain ⟨W, hWc, hW1⟩ := exists_compact_mem_nhds (1 : G)
  set B : Set G := W * (K₁ : Set G) with hBdef
  have hBc : IsCompact B := hWc.mul hK₁
  have hBm : MeasurableSet B := hBc.isClosed.measurableSet
  let b : G → ℝ≥0∞ := fun g => ∫⁻ q, B.indicator 1 (ι q * g) ∂μP
  have hjoint : Measurable (fun z : P × G => B.indicator (1 : G → ℝ≥0∞) (ι z.1 * z.2)) :=
    (measurable_one.indicator hBm).comp
      ((hιc.comp continuous_fst).mul continuous_snd).measurable
  have hb_meas : Measurable b := hjoint.lintegral_prod_left'
  have hslice_meas : ∀ g : G, Measurable (fun q : P => B.indicator (1 : G → ℝ≥0∞) (ι q * g)) :=
    fun g => (measurable_one.indicator hBm).comp ((hιc.mul continuous_const).measurable)
  have hb_eq : ∀ g : G, b g = μP ((fun q : P => ι q * g) ⁻¹' B) := by
    intro g
    have hind : (fun q : P => B.indicator (1 : G → ℝ≥0∞) (ι q * g)) =
        ((fun q : P => ι q * g) ⁻¹' B).indicator 1 := by
      funext q
      rfl
    have hS : MeasurableSet ((fun q : P => ι q * g) ⁻¹' B) :=
      hBm.preimage (hιc.mul continuous_const).measurable
    change ∫⁻ q, (fun q : P => B.indicator (1 : G → ℝ≥0∞) (ι q * g)) q ∂μP = _
    rw [hind]
    exact lintegral_indicator_one hS
  have hb_equiv : ∀ (q₀ : P) (g : G),
      b (ι q₀ * g) = (Measure.modularCharacter q₀ : ℝ≥0∞) * b g := by
    intro q₀ g
    have hrw : ∀ q : P, B.indicator (1 : G → ℝ≥0∞) (ι q * (ι q₀ * g)) =
        B.indicator 1 (ι (q * q₀) * g) := fun q => by rw [map_mul, mul_assoc]
    change ∫⁻ q, B.indicator 1 (ι q * (ι q₀ * g)) ∂μP = _
    simp_rw [hrw]
    have hmap := map_right_mul_eq_modularCharacterFun_smul μP q₀
    calc ∫⁻ q, B.indicator 1 (ι (q * q₀) * g) ∂μP
        = ∫⁻ q, B.indicator 1 (ι q * g) ∂(Measure.map (· * q₀) μP) :=
          (lintegral_map (hslice_meas g) (measurable_mul_const q₀)).symm
      _ = _ := by
          rw [hmap, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
          rfl
  have hb_fin : ∀ g : G, b g ≠ ∞ := by
    intro g
    rw [hb_eq]
    have hc : IsCompact ((fun q : P => ι q * g) ⁻¹' B) := by
      have h1 : IsCompact ((fun x : G => x * g) ⁻¹' B) :=
        (Homeomorph.mulRight g).isCompact_preimage.mpr hBc
      exact hι.isCompact_preimage h1
    exact hc.measure_lt_top.ne
  have hb_pos : ∀ g : G, b g ≠ 0 := by
    intro g
    rw [hb_eq]
    obtain ⟨q₀, k₀, hk₀, rfl⟩ := h₁ g
    have hsub : (fun q : P => ι (q * q₀)) ⁻¹' W ⊆ (fun q : P => ι q * (ι q₀ * k₀)) ⁻¹' B := by
      intro q hq
      refine ⟨ι (q * q₀), hq, k₀, hk₀, ?_⟩
      simp only [map_mul, mul_assoc]
    have hn : (fun q : P => ι (q * q₀)) ⁻¹' W ∈ 𝓝 q₀⁻¹ := by
      have hcont : Continuous (fun q : P => ι (q * q₀)) := hιc.comp (continuous_id.mul continuous_const)
      apply hcont.continuousAt.preimage_mem_nhds
      simpa using hW1
    exact (measure_pos_of_mem_nhds μP (Filter.mem_of_superset hn hsub)).ne'
  -- the test function `f = 1_B φ / b`
  let f : G → ℝ≥0∞ := fun g => B.indicator 1 g * φ g * (b g)⁻¹
  have hf_meas : Measurable f :=
    ((measurable_one.indicator hBm).mul hφ).mul hb_meas.inv
  have hf_slice : ∀ g : G, ∫⁻ q, f (ι q * g) ∂μP = φ g := by
    intro g
    have hpt : ∀ q : P, f (ι q * g) = B.indicator 1 (ι q * g) * (φ g * (b g)⁻¹) := by
      intro q
      have hΔ0 : (Measure.modularCharacter q : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast (Measure.modularCharacterFun_pos q).ne'
      have hΔt : (Measure.modularCharacter q : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
      change B.indicator 1 (ι q * g) * φ (ι q * g) * (b (ι q * g))⁻¹ = _
      rw [hequiv, hb_equiv, ENNReal.mul_inv (Or.inl hΔ0) (Or.inl hΔt)]
      calc B.indicator 1 (ι q * g) * ((Measure.modularCharacter q : ℝ≥0∞) * φ g) *
            ((Measure.modularCharacter q : ℝ≥0∞)⁻¹ * (b g)⁻¹)
          = B.indicator 1 (ι q * g) * (((Measure.modularCharacter q : ℝ≥0∞) *
              (Measure.modularCharacter q : ℝ≥0∞)⁻¹) * (φ g * (b g)⁻¹)) := by ring
        _ = _ := by rw [ENNReal.mul_inv_cancel hΔ0 hΔt, one_mul]
    simp_rw [hpt]
    rw [lintegral_mul_const _ (hslice_meas g)]
    change b g * (φ g * (b g)⁻¹) = φ g
    rw [mul_comm, mul_assoc, ENNReal.inv_mul_cancel (hb_pos g) (hb_fin g), mul_one]
  have e₁ := hint K₁ μ₁ c₁ hμ₁ f hf_meas
  have e₂ := hint K₂ μ₂ c₂ hμ₂ f hf_meas
  simp only [hf_slice] at e₁ e₂
  have hkey : (c₁ : ℝ≥0∞) * ∫⁻ k, φ k ∂μ₁ = (c₂ : ℝ≥0∞) * ∫⁻ k, φ k ∂μ₂ := e₁.symm.trans e₂
  have hc₁0 : (c₁ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc₁.ne'
  rw [ENNReal.coe_div hc₁.ne', ENNReal.div_eq_inv_mul, mul_assoc, ← hkey, ← mul_assoc,
    ENNReal.inv_mul_cancel hc₁0 ENNReal.coe_ne_top, one_mul]

end Langlands.CompactFactorization
