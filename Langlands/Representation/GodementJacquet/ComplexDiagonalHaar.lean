import Langlands.Representation.GodementJacquet.ComplexCoordinateDilation

/-! # The multiplicative Haar density on the complex diagonal torus -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped BigOperators NNReal ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open RankinSelberg.GLDeterminantDensity

variable {ι : Type*} [Fintype ι]
local notation "D" => ι → ℂˣ
local notation "Z" => ι → ℂ

local instance diagonalHaarUnitsMeasurable : MeasurableSpace ℂˣ := borel _
local instance diagonalHaarUnitsBorel : BorelSpace ℂˣ := ⟨rfl⟩
local instance diagonalHaarUnitsSecondCountable : SecondCountableTopology ℂˣ :=
  (Units.isOpenEmbedding_val (R := ℂ)).isInducing.secondCountableTopology

/-- Diagonal unit coordinates viewed as complex additive coordinates. -/
def complexDiagonalVal (d : D) : Z := fun i => (d i : ℂ)

omit [Fintype ι] in
theorem complexDiagonalVal_ne_zero (d : D) (i : ι) : complexDiagonalVal d i ≠ 0 :=
  (d i).ne_zero

omit [Fintype ι] in
@[simp]
theorem complexDiagonalVal_mul (d e : D) :
    complexDiagonalVal (d * e) = complexDiagonalVal d * complexDiagonalVal e := rfl

theorem isOpenEmbedding_complexDiagonalVal : IsOpenEmbedding (complexDiagonalVal (ι := ι)) :=
  IsOpenEmbedding.piMap fun _ => Units.isOpenEmbedding_val

theorem measurableEmbedding_complexDiagonalVal :
    MeasurableEmbedding (complexDiagonalVal (ι := ι)) :=
  isOpenEmbedding_complexDiagonalVal.measurableEmbedding

private def diagonalAbsoluteValue : D →* ℝ≥0ˣ where
  toFun d := ∏ i, Units.map complexAbsHom.toMonoidHom (d i)
  map_one' := by simp
  map_mul' d e := by simp [Finset.prod_mul_distrib]

private def diagonalHaarWeight (d : D) : ℝ≥0 := ((diagonalAbsoluteValue d)⁻¹ : ℝ≥0ˣ).val

private theorem diagonalHaarWeight_eq (d : D) :
    diagonalHaarWeight d = (complexCoordinateJacobian (complexDiagonalVal d))⁻¹ := by
  rw [diagonalHaarWeight, Units.val_inv_eq_inv_val]
  apply congrArg Inv.inv
  exact map_prod (Units.coeHom ℝ≥0) (fun i => Units.map complexAbsHom.toMonoidHom (d i)) Finset.univ

private theorem continuous_diagonalHaarWeight : Continuous (diagonalHaarWeight (ι := ι)) := by
  rw [show diagonalHaarWeight (ι := ι) = _ from funext diagonalHaarWeight_eq]
  apply Continuous.inv₀
  · unfold complexCoordinateJacobian
    exact continuous_finsetProd _ fun i _ => continuous_complexAbsHom.comp
      (Units.continuous_val.comp (continuous_apply i))
  · exact fun d => complexCoordinateJacobian_ne_zero (complexDiagonalVal_ne_zero d)

private def diagonalAdditiveRestriction (a : ℂˣ) : Measure D :=
  (complexCoordinateMeasure ι a).comap complexDiagonalVal

/-- Multiplicative Haar for the diagonal torus, using the same self-dual
scalar additive measure in each factor. -/
def complexDiagonalHaar (a : ℂˣ) : Measure D :=
  (diagonalAdditiveRestriction a).withDensity (fun d => (diagonalHaarWeight d : ℝ≥0∞))

private theorem diagonalAdditiveRestriction_map_mul (a : ℂˣ) (d : D) :
    (diagonalAdditiveRestriction a).map (fun e => d * e) =
      (complexCoordinateJacobian (complexDiagonalVal d))⁻¹ • diagonalAdditiveRestriction a := by
  have he := measurableEmbedding_complexDiagonalVal (ι := ι)
  have hM : Measurable (fun z : Z => complexDiagonalVal d * z) :=
    measurable_const.mul measurable_id
  have hD : Measurable (fun e : D => d * e) := (continuous_const.mul continuous_id).measurable
  have hpre (T : Set D) :
      complexDiagonalVal '' ((fun e => d * e) ⁻¹' T) =
        (fun z => complexDiagonalVal d * z) ⁻¹' (complexDiagonalVal '' T) := by
    ext z
    constructor
    · rintro ⟨e, he', rfl⟩
      exact ⟨d * e, he', rfl⟩
    · rintro ⟨e, he', hz⟩
      refine ⟨d⁻¹ * e, ?_, ?_⟩
      · change d * (d⁻¹ * e) ∈ T
        rwa [mul_inv_cancel_left]
      · funext i
        apply mul_left_cancel₀ (complexDiagonalVal_ne_zero d i)
        change complexDiagonalVal (d * (d⁻¹ * e)) i = _
        rw [mul_inv_cancel_left]
        exact congrFun hz i
  ext T hT
  rw [Measure.map_apply hD hT, diagonalAdditiveRestriction, he.comap_apply, hpre,
    ← Measure.map_apply hM (he.measurableSet_image.mpr hT),
    map_complexCoordinateMul a (complexDiagonalVal d) (complexDiagonalVal_ne_zero d)]
  simp only [Measure.smul_apply, he.comap_apply]

private theorem complexDiagonalHaar_isMulLeftInvariant (a : ℂˣ) :
    (complexDiagonalHaar (ι := ι) a).IsMulLeftInvariant := by
  constructor
  intro d
  change (complexDiagonalHaar a).map (MeasurableEquiv.mulLeft d) = _
  rw [complexDiagonalHaar, map_withDensity_equiv]
  change ((diagonalAdditiveRestriction a).map (fun e => d * e)).withDensity
    (fun e => (diagonalHaarWeight (d⁻¹ * e) : ℝ≥0∞)) = _
  rw [diagonalAdditiveRestriction_map_mul, ← diagonalHaarWeight_eq]
  have h (e : D) : diagonalHaarWeight (d⁻¹ * e) =
      (diagonalHaarWeight d)⁻¹ * diagonalHaarWeight e := by
    simp only [diagonalHaarWeight, map_mul, map_inv, mul_inv, inv_inv, Units.val_mul,
      Units.val_inv_eq_inv_val]
  have h₀ : diagonalHaarWeight d ≠ 0 := ((diagonalAbsoluteValue d)⁻¹).ne_zero
  have hw : Measurable (fun e : D => (diagonalHaarWeight e : ℝ≥0∞)) :=
    continuous_diagonalHaarWeight.measurable.coe_nnreal_ennreal
  change ((diagonalHaarWeight d : ℝ≥0∞) • diagonalAdditiveRestriction a).withDensity _ = _
  rw [withDensity_smul_measure]
  simp only [h, ENNReal.coe_mul, ENNReal.coe_inv h₀]
  rw [show (fun e : D => (diagonalHaarWeight d : ℝ≥0∞)⁻¹ * (diagonalHaarWeight e : ℝ≥0∞)) =
      ((diagonalHaarWeight d : ℝ≥0∞)⁻¹ • (fun e : D => (diagonalHaarWeight e : ℝ≥0∞)))
      by rfl, withDensity_smul _ hw, smul_smul,
    ENNReal.mul_inv_cancel (by exact_mod_cast h₀) ENNReal.coe_ne_top, one_smul]

instance complexDiagonalHaar_isHaar (a : ℂˣ) : (complexDiagonalHaar (ι := ι) a).IsHaarMeasure := by
  let : LocallyCompactSpace D := isOpenEmbedding_complexDiagonalVal.locallyCompactSpace
  let μ := diagonalAdditiveRestriction (ι := ι) a
  let : IsFiniteMeasureOnCompacts μ := IsFiniteMeasureOnCompacts.comap' _
    isOpenEmbedding_complexDiagonalVal.continuous measurableEmbedding_complexDiagonalVal
  let : IsOpenPosMeasure μ := IsOpenPosMeasure.comap _ isOpenEmbedding_complexDiagonalVal
  let : IsLocallyFiniteMeasure (complexDiagonalHaar (ι := ι) a) :=
    IsLocallyFiniteMeasure.withDensity_coe continuous_diagonalHaarWeight
  let : (complexDiagonalHaar (ι := ι) a).IsMulLeftInvariant := complexDiagonalHaar_isMulLeftInvariant a
  refine { lt_top_of_isCompact := fun _ h => h.measure_lt_top, open_pos := ?_ }
  intro S hS hn hz
  have h := (withDensity_apply_eq_zero (μ := μ) (s := S)
    continuous_diagonalHaarWeight.measurable.coe_nnreal_ennreal).mp hz
  have hs : {d : D | (diagonalHaarWeight d : ℝ≥0∞) ≠ 0} = univ := by
    exact eq_univ_of_forall fun d => ENNReal.coe_ne_zero.mpr ((diagonalAbsoluteValue d)⁻¹).ne_zero
  rw [hs, univ_inter] at h
  exact hS.measure_ne_zero μ hn h

instance complexDiagonalHaar_sigmaFinite (a : ℂˣ) :
    SigmaFinite (complexDiagonalHaar (ι := ι) a) := by
  let : LocallyCompactSpace D := isOpenEmbedding_complexDiagonalVal.locallyCompactSpace
  let : SecondCountableTopology D :=
    isOpenEmbedding_complexDiagonalVal.isInducing.secondCountableTopology
  infer_instance

/-- In complex additive coordinates the torus measure has the product inverse
squared-norm density. -/
theorem complexDiagonalHaar_map (a : ℂˣ) :
    (complexDiagonalHaar (ι := ι) a).map complexDiagonalVal =
      (complexCoordinateMeasure ι a).withDensity
        (fun z => (((complexCoordinateJacobian z)⁻¹ : ℝ≥0) : ℝ≥0∞)) := by
  let w (z : Z) := (((complexCoordinateJacobian z)⁻¹ : ℝ≥0) : ℝ≥0∞)
  calc
    _ = ((diagonalAdditiveRestriction a).map complexDiagonalVal).withDensity w := by
      simpa only [complexDiagonalHaar, diagonalHaarWeight_eq] using
        map_withDensity_comp (diagonalAdditiveRestriction a) measurableEmbedding_complexDiagonalVal w
    _ = _ := by
      congr 1
      rw [diagonalAdditiveRestriction, measurableEmbedding_complexDiagonalVal.map_comap]
      apply Measure.restrict_eq_self_of_ae_mem
      filter_upwards [ae_complexCoordinate_ne_zero (ι := ι) a] with z hz
      exact ⟨fun i => Units.mk0 (z i) (hz i), rfl⟩

end Langlands.GodementJacquet
