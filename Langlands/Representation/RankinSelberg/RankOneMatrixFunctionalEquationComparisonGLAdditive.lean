import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLDensity
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFramedIntegrability

/-! # Cancelling determinant density for the actual GL Haar measure -/

noncomputable section

namespace Langlands.RankinSelberg.GLDeterminantDensity

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear
open scoped NNReal ENNReal

universe uK uF uE uH

section Algebra

variable {K : Type uK} [Field K] (r : ℕ) (χ : K →*₀ ℝ≥0)

/-- The positive natural determinant power that cancels the GL Haar density. -/
def forwardWeight (X : Matrix (Fin r) (Fin r) K) : ℝ≥0 :=
  χ X.det ^ r

theorem matrixWeight_mul_forwardWeight
    (g : Langlands.GeneralLinear r K) :
    matrixWeight r χ g.val * forwardWeight r χ g.val = 1 := by
  have hn : χ g.val.det ≠ 0 :=
    (show IsUnit (χ g.val.det) from
      Units.isUnit (((Units.map χ.toMonoidHom).comp GeneralLinear.determinant) g)).ne_zero
  rw [matrixWeight, forwardWeight, inv_pow, inv_mul_cancel₀ (pow_ne_zero r hn)]

end Algebra

section General

variable {K : Type uK} [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T2Space K] (r : ℕ) (χ : K →*₀ ℝ≥0)
  [MeasurableSpace (Matrix (Fin r) (Fin r) K)]
  [BorelSpace (Matrix (Fin r) (Fin r) K)]
  [MeasurableSpace (Langlands.GeneralLinear r K)]
  [BorelSpace (Langlands.GeneralLinear r K)]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [MeasurableSpace (Langlands.GeneralLinear r K)]
  [BorelSpace (Langlands.GeneralLinear r K)] in
private theorem density_cancel_ae
    (μ : Measure (Matrix (Fin r) (Fin r) K))
    (A : Matrix (Fin r) (Fin r) K → E) :
    (fun X => matrixWeight r χ X • (forwardWeight r χ X • A X)) =ᵐ[
      μ.restrict (Set.range (Units.val : Langlands.GeneralLinear r K →
        Matrix (Fin r) (Fin r) K))] A := by
  filter_upwards [ae_restrict_mem
    (isOpenEmbedding_generalLinear_val (K := K) r).isOpen_range.measurableSet]
    with X hX
  obtain ⟨g, rfl⟩ := hX
  rw [smul_smul, matrixWeight_mul_forwardWeight, one_smul]

/-- Cancellation of the inverse determinant density preserves genuine
integrability, with the original additive measure restricted to invertibles. -/
theorem integrable_forwardWeight_iff_of_eq_smul
    (hχ : Continuous χ) (μ : Measure (Matrix (Fin r) (Fin r) K))
    (η : Measure (Langlands.GeneralLinear r K)) (c : ℝ≥0) (hc : 0 < c)
    (heq : weightedRestriction r χ μ = c • η)
    (A : Matrix (Fin r) (Fin r) K → E) :
    Integrable (fun g : Langlands.GeneralLinear r K =>
      forwardWeight r χ g.val • A g.val) η ↔
    Integrable A (μ.restrict (Set.range (Units.val : Langlands.GeneralLinear r K →
      Matrix (Fin r) (Fin r) K))) := by
  have h := integrable_weightedRestriction_iff r χ hχ μ
    (fun X => forwardWeight r χ X • A X)
  rw [heq] at h
  change Integrable (fun g : Langlands.GeneralLinear r K =>
    forwardWeight r χ g.val • A g.val)
    ((c : ℝ≥0∞) • η) ↔ _ at h
  rw [integrable_smul_measure (by exact_mod_cast hc.ne') ENNReal.coe_ne_top] at h
  exact h.trans (integrable_congr (density_cancel_ae r χ μ A))

/-- The exact scalar in Haar uniqueness survives density cancellation and is
independent of the function being integrated. -/
theorem integral_forwardWeight_of_eq_smul
    (hχ : Continuous χ) (μ : Measure (Matrix (Fin r) (Fin r) K))
    (η : Measure (Langlands.GeneralLinear r K)) (c : ℝ≥0) (hc : 0 < c)
    (heq : weightedRestriction r χ μ = c • η)
    (A : Matrix (Fin r) (Fin r) K → E) :
    (∫ g : Langlands.GeneralLinear r K,
      forwardWeight r χ g.val • A g.val ∂η) =
    c⁻¹ • ∫ X, A X ∂μ.restrict
      (Set.range (Units.val : Langlands.GeneralLinear r K →
        Matrix (Fin r) (Fin r) K)) := by
  have h := integral_weightedRestriction r χ hχ μ
    (fun X => forwardWeight r χ X • A X)
  rw [heq, integral_smul_nnreal_measure,
    integral_congr_ae (density_cancel_ae r χ μ A)] at h
  rw [← h, inv_smul_smul₀ hc.ne']


section Product

variable {H : Type uH} [MeasurableSpace H]

private theorem product_weightedRestriction_map
    (hχ : Continuous χ) (μH : Measure H) [SFinite μH]
    (μ : Measure (Matrix (Fin r) (Fin r) K)) [SFinite μ]
    [SFinite (weightedRestriction r χ μ)] :
    (μH.prod (weightedRestriction r χ μ)).map
        (Prod.map id (Units.val : Langlands.GeneralLinear r K →
          Matrix (Fin r) (Fin r) K)) =
      (μH.prod (μ.restrict (Set.range (Units.val : Langlands.GeneralLinear r K →
        Matrix (Fin r) (Fin r) K)))).withDensity
        (fun z => (matrixWeight r χ z.2 : ℝ≥0∞)) := by
  have he := (isOpenEmbedding_generalLinear_val (K := K) r).measurableEmbedding
  rw [← Measure.map_prod_map μH (weightedRestriction r χ μ) measurable_id he.measurable,
    Measure.map_id, weightedRestriction_map,
    prod_withDensity_right (measurable_matrixWeight r χ hχ).coe_nnreal_ennreal]

omit [MeasurableSpace (Langlands.GeneralLinear r K)]
  [BorelSpace (Langlands.GeneralLinear r K)] in
private theorem product_density_cancel_ae
    (μH : Measure H) (μ : Measure (Matrix (Fin r) (Fin r) K)) [SFinite μ]
    (A : H × Matrix (Fin r) (Fin r) K → E) :
    (fun z => matrixWeight r χ z.2 • (forwardWeight r χ z.2 • A z)) =ᵐ[
      μH.prod (μ.restrict (Set.range (Units.val : Langlands.GeneralLinear r K →
        Matrix (Fin r) (Fin r) K)))] A := by
  have hmem := Measure.quasiMeasurePreserving_snd (μ := μH)
    (ν := μ.restrict (Set.range (Units.val : Langlands.GeneralLinear r K →
      Matrix (Fin r) (Fin r) K))) |>.ae
        (ae_restrict_mem (isOpenEmbedding_generalLinear_val (K := K) r
          ).isOpen_range.measurableSet)
  filter_upwards [hmem] with z hz
  obtain ⟨g, hg⟩ := hz
  rw [← hg, smul_smul, matrixWeight_mul_forwardWeight, one_smul]

/-- Joint convergence transfers to the same product additive measure restricted
in the matrix variable. No inference from convergence of an averaged integral is used. -/
theorem integrable_prod_forwardWeight_iff_of_eq_smul
    (hχ : Continuous χ) (μH : Measure H) [SFinite μH]
    (μ : Measure (Matrix (Fin r) (Fin r) K)) [SFinite μ]
    (η : Measure (Langlands.GeneralLinear r K)) [SFinite η]
    (c : ℝ≥0) (hc : 0 < c) (heq : weightedRestriction r χ μ = c • η)
    (A : H × Matrix (Fin r) (Fin r) K → E) :
    Integrable (fun z : H × Langlands.GeneralLinear r K =>
      forwardWeight r χ z.2.val • A (z.1, z.2.val)) (μH.prod η) ↔
    Integrable A (μH.prod (μ.restrict
      (Set.range (Units.val : Langlands.GeneralLinear r K →
        Matrix (Fin r) (Fin r) K)))) := by
  let : SFinite (weightedRestriction r χ μ) := by rw [heq]; infer_instance
  have he : MeasurableEmbedding (Prod.map (id : H → H)
      (Units.val : Langlands.GeneralLinear r K → Matrix (Fin r) (Fin r) K)) :=
    MeasurableEmbedding.id.prodMap
      (isOpenEmbedding_generalLinear_val (K := K) r).measurableEmbedding
  have h := he.integrable_map_iff (μ := μH.prod (weightedRestriction r χ μ))
    (g := fun z => forwardWeight r χ z.2 • A z)
  rw [product_weightedRestriction_map r χ hχ μH μ,
    integrable_withDensity_iff_integrable_smul
      (show Measurable (fun z : H × Matrix (Fin r) (Fin r) K =>
        matrixWeight r χ z.2) from
          (measurable_matrixWeight r χ hχ).comp measurable_snd)] at h
  rw [heq, Measure.prod_smul_right] at h
  change _ ↔ Integrable (fun z : H × Langlands.GeneralLinear r K =>
    forwardWeight r χ z.2.val • A (z.1, z.2.val))
      ((c : ℝ≥0∞) • (μH.prod η)) at h
  rw [integrable_smul_measure (by exact_mod_cast hc.ne') ENNReal.coe_ne_top] at h
  exact h.symm.trans (integrable_congr (product_density_cancel_ae r χ μH μ A))

/-- Product integral version of determinant-density cancellation, with the
single fixed Haar-normalization scalar retained. -/
theorem integral_prod_forwardWeight_of_eq_smul
    (hχ : Continuous χ) (μH : Measure H) [SFinite μH]
    (μ : Measure (Matrix (Fin r) (Fin r) K)) [SFinite μ]
    (η : Measure (Langlands.GeneralLinear r K)) [SFinite η]
    (c : ℝ≥0) (hc : 0 < c) (heq : weightedRestriction r χ μ = c • η)
    (A : H × Matrix (Fin r) (Fin r) K → E) :
    (∫ z : H × Langlands.GeneralLinear r K,
      forwardWeight r χ z.2.val • A (z.1, z.2.val) ∂μH.prod η) =
    c⁻¹ • ∫ z, A z ∂μH.prod (μ.restrict
      (Set.range (Units.val : Langlands.GeneralLinear r K →
        Matrix (Fin r) (Fin r) K))) := by
  let : SFinite (weightedRestriction r χ μ) := by rw [heq]; infer_instance
  have he : MeasurableEmbedding (Prod.map (id : H → H)
      (Units.val : Langlands.GeneralLinear r K → Matrix (Fin r) (Fin r) K)) :=
    MeasurableEmbedding.id.prodMap
      (isOpenEmbedding_generalLinear_val (K := K) r).measurableEmbedding
  have h := he.integral_map (μ := μH.prod (weightedRestriction r χ μ))
    (fun z => forwardWeight r χ z.2 • A z)
  rw [product_weightedRestriction_map r χ hχ μH μ,
    integral_withDensity_eq_integral_smul
      (show Measurable (fun z : H × Matrix (Fin r) (Fin r) K =>
        matrixWeight r χ z.2) from
          (measurable_matrixWeight r χ hχ).comp measurable_snd),
    integral_congr_ae (product_density_cancel_ae r χ μH μ A),
    heq, Measure.prod_smul_right, integral_smul_nnreal_measure] at h
  change _ = c • ∫ z : H × Langlands.GeneralLinear r K,
    forwardWeight r χ z.2.val • A (z.1, z.2.val) ∂μH.prod η at h
  rw [h, inv_smul_smul₀ hc.ne']

end Product

end General

section CanonicalPadic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance : SigmaCompactSpace F.Carrier := F.canonicalTopologicalData.sigmaCompactSpace
local instance : MeasurableSpace F.Carrier := borel _
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.upperUnipotentLocallyCompactSpace (n + 1)
local instance (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "χ" => F.canonicalTopologicalData.normalizedAbsHom

/-- One fixed positive normalization scalar for the supplied scalar Haar
measure, used for every function and test. -/
def rectangularHaarScalar (ν : AdditiveHaarMeasure F.Carrier) (n : ℕ) : ℝ≥0 :=
  (padic_exists_weightedRestriction_eq_generalLinearHaar
    F F.canonicalTopologicalData n (rectangularMeasure ν (n + 1) (n + 1))).choose

theorem rectangularHaarScalar_pos (ν : AdditiveHaarMeasure F.Carrier) (n : ℕ) :
    0 < rectangularHaarScalar F ν n :=
  (padic_exists_weightedRestriction_eq_generalLinearHaar
    F F.canonicalTopologicalData n (rectangularMeasure ν (n + 1) (n + 1))).choose_spec.1

theorem weightedRestriction_eq_rectangularHaarScalar
    (ν : AdditiveHaarMeasure F.Carrier) (n : ℕ) :
    weightedRestriction (n + 1) χ (rectangularMeasure ν (n + 1) (n + 1)) =
      rectangularHaarScalar F ν n • generalLinearHaar F.Carrier n :=
  (padic_exists_weightedRestriction_eq_generalLinearHaar
    F F.canonicalTopologicalData n (rectangularMeasure ν (n + 1) (n + 1))).choose_spec.2

theorem forwardWeight_eq_determinantWeight (n : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F.Carrier) (z : ℂ) :
    forwardWeight (n + 1) χ g.val • z =
      determinantWeight abv g (n + 1 : ℕ) * z := by
  simp only [forwardWeight, NNReal.smul_def, Complex.real_smul,
    NNReal.coe_pow, Complex.ofReal_pow, determinantWeight, Complex.cpow_natCast]
  rfl

/-- The actual natural matrix-size determinant power converts GL convergence
to additive convergence on the invertible locus, with the same supplied ν. -/
theorem integrable_generalLinearHaar_natWeight_iff
    (ν : AdditiveHaarMeasure F.Carrier) (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier → ℂ) :
    Integrable (fun g : Langlands.GeneralLinear (n + 1) F.Carrier =>
      determinantWeight abv g (n + 1 : ℕ) * A g.val)
      (generalLinearHaar F.Carrier n) ↔
    Integrable A ((rectangularMeasure ν (n + 1) (n + 1)).restrict
      (Set.range (Units.val : Langlands.GeneralLinear (n + 1) F.Carrier →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))) := by
  simpa only [forwardWeight_eq_determinantWeight F] using
    integrable_forwardWeight_iff_of_eq_smul (n + 1) χ
      F.canonicalTopologicalData.continuous_normalizedAbsHom
      (rectangularMeasure ν (n + 1) (n + 1)) (generalLinearHaar F.Carrier n)
      (rectangularHaarScalar F ν n) (rectangularHaarScalar_pos F ν n)
      (weightedRestriction_eq_rectangularHaarScalar F ν n) A

/-- The natural determinant power cancels the density; the one positive
normalization scalar is retained explicitly. -/
theorem integral_generalLinearHaar_natWeight
    (ν : AdditiveHaarMeasure F.Carrier) (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier → ℂ) :
    (∫ g : Langlands.GeneralLinear (n + 1) F.Carrier,
      determinantWeight abv g (n + 1 : ℕ) * A g.val
        ∂generalLinearHaar F.Carrier n) =
    ((rectangularHaarScalar F ν n : ℝ) : ℂ)⁻¹ *
      ∫ X, A X ∂(rectangularMeasure ν (n + 1) (n + 1)).restrict
        (Set.range (Units.val : Langlands.GeneralLinear (n + 1) F.Carrier →
          Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) := by
  simpa only [forwardWeight_eq_determinantWeight F, NNReal.smul_def,
    NNReal.coe_inv, Complex.real_smul, Complex.ofReal_inv] using
    integral_forwardWeight_of_eq_smul (n + 1) χ
      F.canonicalTopologicalData.continuous_normalizedAbsHom
      (rectangularMeasure ν (n + 1) (n + 1)) (generalLinearHaar F.Carrier n)
      (rectangularHaarScalar F ν n) (rectangularHaarScalar_pos F ν n)
      (weightedRestriction_eq_rectangularHaarScalar F ν n) A


/-- Product-measure convergence for the canonical GL measure and supplied ν. -/
theorem integrable_prod_generalLinearHaar_natWeight_iff
    {H : Type uH} [MeasurableSpace H] (μH : Measure H) [SFinite μH]
    (ν : AdditiveHaarMeasure F.Carrier) (n : ℕ)
    (A : H × Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier → ℂ) :
    Integrable (fun z : H × Langlands.GeneralLinear (n + 1) F.Carrier =>
      determinantWeight abv z.2 (n + 1 : ℕ) * A (z.1, z.2.val))
        (μH.prod (generalLinearHaar F.Carrier n)) ↔
    Integrable A (μH.prod ((rectangularMeasure ν (n + 1) (n + 1)).restrict
      (Set.range (Units.val : Langlands.GeneralLinear (n + 1) F.Carrier →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)))) := by
  simpa only [forwardWeight_eq_determinantWeight F] using
    integrable_prod_forwardWeight_iff_of_eq_smul (n + 1) χ
      F.canonicalTopologicalData.continuous_normalizedAbsHom μH
      (rectangularMeasure ν (n + 1) (n + 1)) (generalLinearHaar F.Carrier n)
      (rectangularHaarScalar F ν n) (rectangularHaarScalar_pos F ν n)
      (weightedRestriction_eq_rectangularHaarScalar F ν n) A

/-- The product integral retains the same positive scalar as the single GL
integral, independently of the auxiliary measure and the integrand. -/
theorem integral_prod_generalLinearHaar_natWeight
    {H : Type uH} [MeasurableSpace H] (μH : Measure H) [SFinite μH]
    (ν : AdditiveHaarMeasure F.Carrier) (n : ℕ)
    (A : H × Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier → ℂ) :
    (∫ z : H × Langlands.GeneralLinear (n + 1) F.Carrier,
      determinantWeight abv z.2 (n + 1 : ℕ) * A (z.1, z.2.val)
        ∂μH.prod (generalLinearHaar F.Carrier n)) =
    ((rectangularHaarScalar F ν n : ℝ) : ℂ)⁻¹ *
      ∫ z, A z ∂μH.prod ((rectangularMeasure ν (n + 1) (n + 1)).restrict
        (Set.range (Units.val : Langlands.GeneralLinear (n + 1) F.Carrier →
          Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))) := by
  simpa only [forwardWeight_eq_determinantWeight F, NNReal.smul_def,
    NNReal.coe_inv, Complex.real_smul, Complex.ofReal_inv] using
    integral_prod_forwardWeight_of_eq_smul (n + 1) χ
      F.canonicalTopologicalData.continuous_normalizedAbsHom μH
      (rectangularMeasure ν (n + 1) (n + 1)) (generalLinearHaar F.Carrier n)
      (rectangularHaarScalar F ν n) (rectangularHaarScalar_pos F ν n)
      (weightedRestriction_eq_rectangularHaarScalar F ν n) A

/-- Genuine joint convergence on N × GL follows from the full additive-matrix
box bound and determinant-density cancellation. -/
theorem integrable_unipotent_box_generalLinear_natWeight
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (n : ℕ)
    (Φ₁ Φ₂ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (A q : ℤ) {a : ℕ} (ha : 0 < a)
    (hΦ₂ : tsupport (Φ₂ : _ → ℂ) ⊆ RankOneBox.box F A q a)
    (b : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier → ℂ) (hb : Continuous b) :
    Integrable (fun z : upperUnipotent (n + 1) F.Carrier ×
        Langlands.GeneralLinear (n + 1) F.Carrier =>
      determinantWeight abv z.2 (n + 1 : ℕ) *
        ((((standardCharacter ψ n z.1)⁻¹ : ℂˣ) : ℂ) *
          Φ₁ (z.1.val.val * z.2.val) * Φ₂ z.2.val * b z.2.val))
      ((unipotentHaar F.Carrier n).prod (generalLinearHaar F.Carrier n)) := by
  apply (integrable_prod_generalLinearHaar_natWeight_iff F
    (unipotentHaar F.Carrier n) ν n
      (fun z : upperUnipotent (n + 1) F.Carrier ×
          Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier =>
        (((standardCharacter ψ n z.1)⁻¹ : ℂˣ) : ℂ) *
          Φ₁ (z.1.val.val * z.2) * Φ₂ z.2 * b z.2)).2
  exact (CompactWhittakerSynthesis.integrable_unipotent_box_matrix_product F ψ n
    (rectangularMeasure ν (n + 1) (n + 1)) Φ₁ Φ₂ A q ha hΦ₂ b hb).mono_measure
      (Measure.prod_mono le_rfl Measure.restrict_le_self)

/-- Fubini for the actual N and GL Haar measures at the natural determinant
exponent, including matrix size one. -/
theorem integral_unipotent_box_generalLinear_natWeight_swap
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (n : ℕ)
    (Φ₁ Φ₂ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (A q : ℤ) {a : ℕ} (ha : 0 < a)
    (hΦ₂ : tsupport (Φ₂ : _ → ℂ) ⊆ RankOneBox.box F A q a)
    (b : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier → ℂ) (hb : Continuous b) :
    (∫ u : upperUnipotent (n + 1) F.Carrier,
      ∫ g : Langlands.GeneralLinear (n + 1) F.Carrier,
        determinantWeight abv g (n + 1 : ℕ) *
          ((((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) *
            Φ₁ (u.val.val * g.val) * Φ₂ g.val * b g.val)
        ∂generalLinearHaar F.Carrier n ∂unipotentHaar F.Carrier n) =
    ∫ g : Langlands.GeneralLinear (n + 1) F.Carrier,
      ∫ u : upperUnipotent (n + 1) F.Carrier,
        determinantWeight abv g (n + 1 : ℕ) *
          ((((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) *
            Φ₁ (u.val.val * g.val) * Φ₂ g.val * b g.val)
        ∂unipotentHaar F.Carrier n ∂generalLinearHaar F.Carrier n :=
  integral_integral_swap
    (integrable_unipotent_box_generalLinear_natWeight F ψ ν n Φ₁ Φ₂ A q ha hΦ₂ b hb)

end CanonicalPadic

end Langlands.RankinSelberg.GLDeterminantDensity
