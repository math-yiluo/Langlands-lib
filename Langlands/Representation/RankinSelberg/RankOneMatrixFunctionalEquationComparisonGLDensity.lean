import Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
import Langlands.Representation.RankinSelberg.Measures
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.WithDensity

/-! The determinant density relating matrix additive Haar and actual GL Haar. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology
open scoped NNReal ENNReal

namespace Langlands.RankinSelberg.GLDeterminantDensity

universe uK

section Measure

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Push a pulled-back density through a measurable embedding. -/
theorem map_withDensity_comp (μ : Measure X) {e : X → Y}
    (he : MeasurableEmbedding e) (w : Y → ℝ≥0∞) :
    (μ.withDensity (fun x => w (e x))).map e = (μ.map e).withDensity w := by
  ext s hs
  rw [he.map_apply, withDensity_apply _ (he.measurable hs), withDensity_apply _ hs,
    he.restrict_map, he.lintegral_map]

/-- Transport a density through a measurable equivalence. -/
theorem map_withDensity_equiv (μ : Measure X) (e : X ≃ᵐ Y) (w : X → ℝ≥0∞) :
    (μ.withDensity w).map e = (μ.map e).withDensity (fun y => w (e.symm y)) := by
  convert map_withDensity_comp μ e.measurableEmbedding (fun y => w (e.symm y)) using 1
  simp only [e.symm_apply_apply]

end Measure

section Algebra

variable {K : Type uK} [Field K] (r : ℕ)

variable (χ : K →*₀ ℝ≥0)

/-- The inverse determinant density on all matrices; only its restriction to
invertible matrices is used for the GL measure. -/
def matrixWeight (X : Matrix (Fin r) (Fin r) K) : ℝ≥0 :=
  (χ X.det)⁻¹ ^ r

/-- The inverse determinant density on GL, with exponent the matrix size. -/
def weight (g : GeneralLinear r K) : ℝ≥0 :=
  (((((Units.map χ.toMonoidHom).comp GeneralLinear.determinant) g)⁻¹ ^
    r : ℝ≥0ˣ) : ℝ≥0)

@[simp]
theorem weight_eq (g : GeneralLinear r K) :
    weight r χ g = (χ g.val.det)⁻¹ ^ r := by
  simp only [weight, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  rfl

theorem weight_ne_zero (g : GeneralLinear r K) : weight r χ g ≠ 0 :=
  (show IsUnit (weight r χ g) from Units.isUnit _).ne_zero

@[simp]
theorem weight_mul (g h : GeneralLinear r K) :
    weight r χ (g * h) = weight r χ g * weight r χ h := by
  simp only [weight, map_mul, mul_inv, mul_pow, Units.val_mul]

@[simp]
theorem weight_inv (g : GeneralLinear r K) :
    weight r χ g⁻¹ = (weight r χ g)⁻¹ := by
  change ((((((Units.map χ.toMonoidHom).comp GeneralLinear.determinant) g⁻¹)⁻¹ ^
    r : ℝ≥0ˣ) : ℝ≥0)) = _
  simp only [map_inv, inv_inv, weight, inv_pow, Units.val_inv_eq_inv_val, inv_inv]

end Algebra

section Topology

variable {K : Type uK} [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] (r : ℕ) (χ : K →*₀ ℝ≥0)

theorem continuous_weight (hχ : Continuous χ) : Continuous (weight r χ) := by
  exact Units.continuous_val.comp
    ((hχ.units_map.comp Matrix.GeneralLinearGroup.continuous_det).inv.pow r)

/-- Measurability suffices even though the inverse determinant need not extend
continuously across singular matrices. -/
theorem measurable_matrixWeight
    [MeasurableSpace (Matrix (Fin r) (Fin r) K)]
    [BorelSpace (Matrix (Fin r) (Fin r) K)] (hχ : Continuous χ) :
    Measurable (matrixWeight r χ) := by
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  exact ((hχ.measurable.comp continuous_id.matrix_det.measurable).inv).pow_const r

end Topology

section General

variable {K : Type uK} [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T2Space K]
  (r : ℕ)
  [MeasurableSpace (Matrix (Fin r) (Fin r) K)]
  [BorelSpace (Matrix (Fin r) (Fin r) K)]
  [MeasurableSpace (GeneralLinear r K)] [BorelSpace (GeneralLinear r K)]

/-- Additive matrix measure restricted to the actual open invertible locus,
pulled back to the matrix unit group. -/
def additiveRestriction (μ : Measure (Matrix (Fin r) (Fin r) K)) :
    Measure (GeneralLinear r K) :=
  μ.comap Units.val

theorem additiveRestriction_map_left
    (μ : Measure (Matrix (Fin r) (Fin r) K))
    (g : GeneralLinear r K) (c : ℝ≥0)
    (hscale : μ.map (fun X => g.val * X) = c • μ) :
    (additiveRestriction r μ).map (fun h => g * h) = c • additiveRestriction r μ := by
  have he := (isOpenEmbedding_generalLinear_val (K := K) r).measurableEmbedding
  have hm : Measurable (fun X : Matrix (Fin r) (Fin r) K => g.val * X) :=
    (continuous_const.mul continuous_id).measurable
  have hsets (s : Set (GeneralLinear r K)) :
      Units.val '' ((fun h => g * h) ⁻¹' s) =
        (fun X => g.val * X) ⁻¹' (Units.val '' s) := by
    ext X
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨g * h, hh, rfl⟩
    · rintro ⟨h, hh, hX⟩
      refine ⟨g⁻¹ * h, ?_, ?_⟩
      · change g * (g⁻¹ * h) ∈ s
        simpa only [mul_inv_cancel_left] using hh
      · change (g⁻¹).val * h.val = X
        rw [hX]
        change (g⁻¹).val * (g.val * X) = X
        rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mul]
  have hg : Measurable (fun h : GeneralLinear r K => g * h) :=
    (continuous_const.mul continuous_id).measurable
  ext s hs
  rw [Measure.map_apply hg hs,
    additiveRestriction, he.comap_apply, hsets,
    ← Measure.map_apply hm (he.measurableSet_image.mpr hs), hscale]
  simp only [Measure.smul_apply, he.comap_apply]

variable (χ : K →*₀ ℝ≥0)

/-- The candidate multiplicative Haar measure obtained from additive matrix measure. -/
def weightedRestriction (μ : Measure (Matrix (Fin r) (Fin r) K)) :
    Measure (GeneralLinear r K) :=
  (additiveRestriction r μ).withDensity (fun g => (weight r χ g : ℝ≥0∞))

theorem weightedRestriction_leftInvariant
    (hχ : Continuous χ) (μ : Measure (Matrix (Fin r) (Fin r) K))
    (hscale : ∀ g : GeneralLinear r K,
      μ.map (fun X => g.val * X) = weight r χ g • μ) :
    IsMulLeftInvariant (weightedRestriction r χ μ) := by
  have hw : Measurable (fun g => (weight r χ g : ℝ≥0∞)) :=
    (continuous_weight r χ hχ).measurable.coe_nnreal_ennreal
  constructor
  intro g
  change (weightedRestriction r χ μ).map (MeasurableEquiv.mulLeft g) = _
  rw [weightedRestriction, map_withDensity_equiv]
  change ((additiveRestriction r μ).map (fun h => g * h)).withDensity
    (fun h => (weight r χ (g⁻¹ * h) : ℝ≥0∞)) = _
  rw [additiveRestriction_map_left r μ g _ (hscale g)]
  change ((weight r χ g : ℝ≥0∞) • additiveRestriction r μ).withDensity
    (fun h => (weight r χ (g⁻¹ * h) : ℝ≥0∞)) = _
  rw [withDensity_smul_measure]
  simp only [weight_mul, weight_inv, ENNReal.coe_mul,
    ENNReal.coe_inv (weight_ne_zero r χ g)]
  rw [show (fun h : GeneralLinear r K =>
      (weight r χ g : ℝ≥0∞)⁻¹ * (weight r χ h : ℝ≥0∞)) =
      ((weight r χ g : ℝ≥0∞)⁻¹ •
        (fun h : GeneralLinear r K => (weight r χ h : ℝ≥0∞))) by rfl,
    withDensity_smul _ hw, smul_smul]
  rw [ENNReal.mul_inv_cancel (by exact_mod_cast weight_ne_zero r χ g)
    ENNReal.coe_ne_top, one_smul]

theorem weightedRestriction_isHaar
    [LocallyCompactSpace (GeneralLinear r K)]
    (hχ : Continuous χ) (μ : Measure (Matrix (Fin r) (Fin r) K))
    [IsFiniteMeasureOnCompacts μ] [IsOpenPosMeasure μ]
    (hscale : ∀ g : GeneralLinear r K,
      μ.map (fun X => g.val * X) = weight r χ g • μ) :
    IsHaarMeasure (weightedRestriction r χ μ) := by
  have he := isOpenEmbedding_generalLinear_val (K := K) r
  let : IsFiniteMeasureOnCompacts (additiveRestriction r μ) :=
    IsFiniteMeasureOnCompacts.comap' μ he.continuous he.measurableEmbedding
  let : IsOpenPosMeasure (additiveRestriction r μ) :=
    IsOpenPosMeasure.comap μ he
  let : IsLocallyFiniteMeasure (weightedRestriction r χ μ) :=
    IsLocallyFiniteMeasure.withDensity_coe (continuous_weight r χ hχ)
  let : IsMulLeftInvariant (weightedRestriction r χ μ) :=
    weightedRestriction_leftInvariant r χ hχ μ hscale
  refine { lt_top_of_isCompact := fun _ h => h.measure_lt_top, open_pos := ?_ }
  intro U hU hUne
  change (additiveRestriction r μ).withDensity _ U ≠ 0
  intro hzero
  have hz := (withDensity_apply_eq_zero (μ := additiveRestriction r μ) (s := U)
    (f := fun g : GeneralLinear r K => (weight r χ g : ℝ≥0∞))
    (continuous_weight r χ hχ).measurable.coe_nnreal_ennreal).mp hzero
  have hsupport : {g : GeneralLinear r K | (weight r χ g : ℝ≥0∞) ≠ 0} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro g
    exact ENNReal.coe_ne_zero.mpr (weight_ne_zero r χ g)
  rw [hsupport, Set.univ_inter] at hz
  exact hU.measure_ne_zero (additiveRestriction r μ) hUne hz

/-- Pushing the weighted measure to matrices gives exactly the determinant
density on the invertible locus. No assertion about the singular locus is needed. -/
theorem weightedRestriction_map (μ : Measure (Matrix (Fin r) (Fin r) K)) :
    (weightedRestriction r χ μ).map Units.val =
      (μ.restrict (Set.range (Units.val : GeneralLinear r K →
        Matrix (Fin r) (Fin r) K))).withDensity
        (fun X => (matrixWeight r χ X : ℝ≥0∞)) := by
  have he := (isOpenEmbedding_generalLinear_val (K := K) r).measurableEmbedding
  unfold weightedRestriction
  simp_rw [weight_eq]
  change ((additiveRestriction r μ).withDensity
    (fun g => (matrixWeight r χ g.val : ℝ≥0∞))).map Units.val = _
  rw [map_withDensity_comp (additiveRestriction r μ) he
    (fun X : Matrix (Fin r) (Fin r) K => (matrixWeight r χ X : ℝ≥0∞))]
  change ((μ.comap Units.val).map Units.val).withDensity _ = _
  rw [he.map_comap]

/-- The same pushforward as a density on the full additive matrix measure. -/
theorem weightedRestriction_map_ambient (μ : Measure (Matrix (Fin r) (Fin r) K)) :
    (weightedRestriction r χ μ).map Units.val =
      μ.withDensity ((Set.range (Units.val : GeneralLinear r K →
        Matrix (Fin r) (Fin r) K)).indicator
        (fun X => (matrixWeight r χ X : ℝ≥0∞))) := by
  rw [weightedRestriction_map, withDensity_indicator
    (isOpenEmbedding_generalLinear_val (K := K) r).isOpen_range.measurableSet]

/-- Uniqueness compares this weighted measure with any actual GL Haar measure
by a strictly positive finite real scalar. -/
theorem exists_weightedRestriction_eq_smul
    [LocallyCompactSpace (GeneralLinear r K)] [SecondCountableTopology (GeneralLinear r K)]
    (hχ : Continuous χ) (μ : Measure (Matrix (Fin r) (Fin r) K))
    [IsFiniteMeasureOnCompacts μ] [IsOpenPosMeasure μ]
    (hscale : ∀ g : GeneralLinear r K,
      μ.map (fun X => g.val * X) = weight r χ g • μ)
    (η : Measure (GeneralLinear r K)) [IsHaarMeasure η] :
    ∃ c : ℝ≥0, 0 < c ∧ weightedRestriction r χ μ = c • η := by
  let : IsHaarMeasure (weightedRestriction r χ μ) :=
    weightedRestriction_isHaar r χ hχ μ hscale
  exact ⟨haarScalarFactor (weightedRestriction r χ μ) η,
    haarScalarFactor_pos_of_isHaarMeasure _ _, isMulLeftInvariant_eq_smul _ _⟩

end General

section Integrals

variable {K : Type uK} [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T2Space K] (r : ℕ) (χ : K →*₀ ℝ≥0)
  [MeasurableSpace (Matrix (Fin r) (Fin r) K)]
  [BorelSpace (Matrix (Fin r) (Fin r) K)]
  [MeasurableSpace (GeneralLinear r K)] [BorelSpace (GeneralLinear r K)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Absolute convergence is transported through the same determinant density. -/
theorem integrable_weightedRestriction_iff (hχ : Continuous χ)
    (μ : Measure (Matrix (Fin r) (Fin r) K)) (f : Matrix (Fin r) (Fin r) K → E) :
    Integrable (fun g : GeneralLinear r K => f g.val) (weightedRestriction r χ μ) ↔
      Integrable (fun X => matrixWeight r χ X • f X)
        (μ.restrict (Set.range (Units.val : GeneralLinear r K →
          Matrix (Fin r) (Fin r) K))) := by
  have he := (isOpenEmbedding_generalLinear_val (K := K) r).measurableEmbedding
  have h := he.integrable_map_iff (μ := weightedRestriction r χ μ) (g := f)
  rw [weightedRestriction_map,
    integrable_withDensity_iff_integrable_smul (measurable_matrixWeight r χ hχ)] at h
  exact h.symm

/-- The Bochner integral formula retains the supplied additive measure and
restricts only to the actual invertible locus. -/
theorem integral_weightedRestriction (hχ : Continuous χ)
    (μ : Measure (Matrix (Fin r) (Fin r) K)) (f : Matrix (Fin r) (Fin r) K → E) :
    (∫ g : GeneralLinear r K, f g.val ∂weightedRestriction r χ μ) =
      ∫ X, matrixWeight r χ X • f X
        ∂μ.restrict (Set.range (Units.val : GeneralLinear r K →
          Matrix (Fin r) (Fin r) K)) := by
  have he := (isOpenEmbedding_generalLinear_val (K := K) r).measurableEmbedding
  rw [← he.integral_map f, weightedRestriction_map,
    integral_withDensity_eq_integral_smul (measurable_matrixWeight r χ hχ)]

end Integrals

universe uF

/-- The genuine residue-normalized determinant density gives Haar measure for
every supplied p-adic realization and every additive matrix Haar measure. -/
theorem padic_weightedRestriction_isHaar {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (r : ℕ) :
    letI := T.topology
    ∀ [MeasurableSpace (Matrix (Fin r) (Fin r) F.Carrier)]
      [BorelSpace (Matrix (Fin r) (Fin r) F.Carrier)]
      [MeasurableSpace (GeneralLinear r F.Carrier)] [BorelSpace (GeneralLinear r F.Carrier)]
      (μ : Measure (Matrix (Fin r) (Fin r) F.Carrier)) [IsAddHaarMeasure μ],
      IsHaarMeasure (weightedRestriction r T.normalizedAbsHom μ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let : LocallyCompactSpace (GeneralLinear r F.Carrier) := T.generalLinearLocallyCompactSpace r
  intro _ _ _ _ μ _
  apply weightedRestriction_isHaar r T.normalizedAbsHom T.continuous_normalizedAbsHom μ
  intro g
  have h := HarmonicAnalysis.padicRectangularHaarScaling F T r r μ g 1
  simp only [inv_one, Units.val_one, Matrix.mul_one, map_one, one_pow, div_one] at h
  rw [weight_eq, inv_pow]
  exact h

/-- Comparison with the canonical actual GL Haar measure, normalized on integral
matrices. The scalar is positive and depends on the supplied additive measure. -/
theorem padic_exists_weightedRestriction_eq_generalLinearHaar {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)]
      [BorelSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)]
      [MeasurableSpace (GeneralLinear (n + 1) F.Carrier)]
      [BorelSpace (GeneralLinear (n + 1) F.Carrier)]
      (μ : Measure (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) [IsAddHaarMeasure μ],
      ∃ c : ℝ≥0, 0 < c ∧ weightedRestriction (n + 1) T.normalizedAbsHom μ =
        c • generalLinearHaar F.Carrier n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : LocallyCompactSpace (GeneralLinear (n + 1) F.Carrier) :=
    T.generalLinearLocallyCompactSpace (n + 1)
  let := T.secondCountableTopology
  let : SecondCountableTopology (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :=
    inferInstanceAs (SecondCountableTopology (Fin (n + 1) → Fin (n + 1) → F.Carrier))
  let : SecondCountableTopology (GeneralLinear (n + 1) F.Carrier) :=
    (isEmbedding_generalLinear_val (K := F.Carrier) (n + 1)).secondCountableTopology
  intro _ _ _ _ μ _
  let : IsHaarMeasure (weightedRestriction (n + 1) T.normalizedAbsHom μ) :=
    padic_weightedRestriction_isHaar F T (n + 1) μ
  exact ⟨haarScalarFactor (weightedRestriction (n + 1) T.normalizedAbsHom μ)
      (generalLinearHaar F.Carrier n), haarScalarFactor_pos_of_isHaarMeasure _ _,
      isMulLeftInvariant_eq_smul _ _⟩

end Langlands.RankinSelberg.GLDeterminantDensity
