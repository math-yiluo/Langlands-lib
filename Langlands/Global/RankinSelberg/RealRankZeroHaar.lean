import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.Representation.GodementJacquet.TateScalarTransport
import Langlands.Representation.RankinSelberg.RankOneQuotient
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Ring.Units

/-! # The quotient measure on `N₁(ℝ) \ GL₁(ℝ)`

At rank one the unipotent subgroup is trivial, and the quotient `N₁(ℝ) \ GL₁(ℝ)` is
homeomorphic to `ℝˣ`. Every compatible quotient measure is a positive multiple of the
multiplicative Haar measure `|x|⁻¹ dx`. See the paired Markdown.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology
open scoped NNReal ENNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealRankZero

open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal

/-- Borel structure on `ℝˣ`. -/
local instance unitsMeasurable : MeasurableSpace ℝˣ := borel _
local instance unitsBorel : BorelSpace ℝˣ := ⟨rfl⟩

local instance rankZeroGLMeasurable : MeasurableSpace (Langlands.GeneralLinear (0 + 1) ℝ) :=
  borel _
local instance rankZeroGLBorel : BorelSpace (Langlands.GeneralLinear (0 + 1) ℝ) := ⟨rfl⟩
local instance rankZeroNMeasurable :
    MeasurableSpace (GeneralLinear.upperUnipotent (0 + 1) ℝ) := borel _
local instance rankZeroNBorel : BorelSpace (GeneralLinear.upperUnipotent (0 + 1) ℝ) := ⟨rfl⟩
local instance rankZeroQMeasurable : MeasurableSpace (LeftUnipotentQuotient 0 ℝ) := borel _
local instance rankZeroQBorel : BorelSpace (LeftUnipotentQuotient 0 ℝ) := ⟨rfl⟩

/-! ### The measure `|x|⁻¹ dx` on `ℝ` and on `ℝˣ` -/

/-- The density `|x|⁻¹`, with value `0` at `x = 0`. -/
def invAbs (x : ℝ) : ℝ≥0 := ‖x‖₊⁻¹

theorem measurable_invAbs : Measurable invAbs :=
  measurable_nnnorm.inv

/-- The measure `|x|⁻¹ dx` on `ℝ`. -/
def invAbsVolume : Measure ℝ := volume.withDensity fun x => (invAbs x : ℝ≥0∞)

theorem invAbsVolume_singleton_zero : invAbsVolume {0} = 0 := by
  rw [invAbsVolume, withDensity_apply _ (measurableSet_singleton 0)]
  simp

theorem measurableEmbedding_val : MeasurableEmbedding (Units.val : ℝˣ → ℝ) :=
  Units.isOpenEmbedding_val.measurableEmbedding

/-- The multiplicative Haar measure `|x|⁻¹ dx` on `ℝˣ`. -/
def unitsHaar : Measure ℝˣ := invAbsVolume.comap Units.val

theorem range_val : Set.range (Units.val : ℝˣ → ℝ) = {0}ᶜ := by
  ext x
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, rfl⟩
    exact u.ne_zero
  · intro hx
    exact ⟨Units.mk0 x hx, rfl⟩

theorem map_val_unitsHaar : unitsHaar.map Units.val = invAbsVolume := by
  rw [unitsHaar, measurableEmbedding_val.map_comap, range_val]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  simpa using invAbsVolume_singleton_zero

/-- Integration against `unitsHaar` is integration against `|x|⁻¹ dx`. -/
theorem integral_unitsHaar (G : ℝ → ℂ) :
    ∫ u, G u ∂unitsHaar = ∫ x, ((|x|⁻¹ : ℝ) : ℂ) * G x := by
  have h := measurableEmbedding_val.integral_map (μ := unitsHaar) G
  rw [map_val_unitsHaar] at h
  rw [← h, invAbsVolume, integral_withDensity_eq_integral_smul measurable_invAbs]
  congr 1

theorem integrable_unitsHaar_iff (G : ℝ → ℂ) :
    Integrable (fun u : ℝˣ => G u) unitsHaar ↔
      Integrable (fun x => ((|x|⁻¹ : ℝ) : ℂ) * G x) := by
  have h := measurableEmbedding_val.integrable_map_iff (μ := unitsHaar) (g := G)
  rw [map_val_unitsHaar] at h
  rw [← Function.comp_def, ← h, invAbsVolume,
    integrable_withDensity_iff_integrable_smul measurable_invAbs]
  apply integrable_congr
  filter_upwards [] with x
  rw [NNReal.smul_def, Complex.real_smul]
  simp [invAbs]

/-- Dilation invariance of `|x|⁻¹ dx`. -/
theorem invAbsVolume_preimage_mul {c : ℝ} (hc : c ≠ 0) {T : Set ℝ} (hT : MeasurableSet T) :
    invAbsVolume ((fun x => c * x) ⁻¹' T) = invAbsVolume T := by
  have hmul : Measurable fun x : ℝ => c * x := measurable_const_mul c
  rw [invAbsVolume, withDensity_apply _ (hmul hT), withDensity_apply _ hT,
    ← lintegral_indicator (hmul hT), ← lintegral_indicator hT]
  set G : ℝ → ℝ≥0∞ := T.indicator fun y => (invAbs y : ℝ≥0∞) * (‖c‖₊ : ℝ≥0∞) with hG
  have hGm : Measurable G :=
    (((measurable_invAbs).coe_nnreal_ennreal).mul_const _).indicator hT
  have hcomp : ((fun x => c * x) ⁻¹' T).indicator (fun x => (invAbs x : ℝ≥0∞)) =
      fun x => G (c * x) := by
    funext x
    by_cases hx : c * x ∈ T
    · have hx' : x ∈ (fun x => c * x) ⁻¹' T := hx
      rw [Set.indicator_of_mem hx', hG, Set.indicator_of_mem hx]
      simp only [invAbs, nnnorm_mul]
      by_cases hx0 : x = 0
      · simp [hx0]
      · have hc' : (‖c‖₊ : ℝ≥0∞) ≠ 0 := by simpa using hc
        have hx'' : (‖x‖₊ : ℝ≥0) ≠ 0 := by simpa using hx0
        rw [mul_inv, ENNReal.coe_mul, mul_comm (((‖c‖₊)⁻¹ : ℝ≥0) : ℝ≥0∞), mul_assoc,
          ← ENNReal.coe_mul, inv_mul_cancel₀ (nnnorm_ne_zero_iff.mpr hc), ENNReal.coe_one,
          mul_one]
    · have hx' : x ∉ (fun x => c * x) ⁻¹' T := hx
      rw [Set.indicator_of_notMem hx', hG, Set.indicator_of_notMem hx]
  have hGeq : G = fun y => T.indicator (fun y => (invAbs y : ℝ≥0∞)) y * (‖c‖₊ : ℝ≥0∞) := by
    funext y
    by_cases hy : y ∈ T <;> simp [hG, hy]
  have hk : ENNReal.ofReal |c⁻¹| * (‖c‖₊ : ℝ≥0∞) = 1 := by
    have h1 : ENNReal.ofReal |c⁻¹| = ((‖c⁻¹‖₊ : ℝ≥0) : ℝ≥0∞) := by
      rw [← Real.norm_eq_abs, ofReal_norm]
      rfl
    rw [h1, ← ENNReal.coe_mul, ← nnnorm_mul, inv_mul_cancel₀ hc, nnnorm_one, ENNReal.coe_one]
  rw [hcomp, ← lintegral_map hGm hmul, Real.map_volume_mul_left hc, lintegral_smul_measure,
    hGeq, lintegral_mul_const _ ((measurable_invAbs.coe_nnreal_ennreal).indicator hT),
    smul_eq_mul, mul_comm, mul_assoc, mul_comm (‖c‖₊ : ℝ≥0∞), hk, mul_one]


/-! ### `unitsHaar` is a Haar measure on `ℝˣ` -/

theorem unitsHaar_apply (S : Set ℝˣ) : unitsHaar S = invAbsVolume (Units.val '' S) :=
  measurableEmbedding_val.comap_apply _ S

theorem image_val_preimage_mul (g : ℝˣ) (S : Set ℝˣ) :
    Units.val '' ((fun u => g * u) ⁻¹' S) =
      (fun x : ℝ => (g : ℝ) * x) ⁻¹' (Units.val '' S) := by
  ext x
  simp only [Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨g * u, hu, Units.val_mul g u⟩
  · rintro ⟨w, hw, hwx⟩
    refine ⟨g⁻¹ * w, by simpa using hw, ?_⟩
    rw [Units.val_mul, hwx, ← mul_assoc, Units.inv_mul, one_mul]

instance unitsHaar_isMulLeftInvariant : unitsHaar.IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  ext S hS
  have hm : Measurable fun u : ℝˣ => g * u :=
    (show Continuous fun u : ℝˣ => g * u from continuous_const.mul continuous_id).measurable
  rw [map_apply hm hS, unitsHaar_apply, unitsHaar_apply,
    image_val_preimage_mul, invAbsVolume_preimage_mul g.ne_zero
      (measurableEmbedding_val.measurableSet_image.mpr hS)]

/-- The compact set of units with value in `[1, 2]`. -/
def unitsIcc : Set ℝˣ := Units.val ⁻¹' Set.Icc 1 2

theorem image_unitsIcc : Units.val '' unitsIcc = Set.Icc (1 : ℝ) 2 := by
  rw [unitsIcc, Set.image_preimage_eq_inter_range, range_val]
  apply Set.inter_eq_left.mpr
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  exact (show (0 : ℝ) < x by linarith [hx.1]).ne'

theorem isCompact_unitsIcc : IsCompact unitsIcc := by
  rw [Units.isOpenEmbedding_val.isInducing.isCompact_iff, image_unitsIcc]
  exact isCompact_Icc

theorem interior_unitsIcc_nonempty : (interior unitsIcc).Nonempty := by
  refine ⟨Units.mk0 (3 / 2) (by norm_num), interior_maximal
    (Set.preimage_mono Set.Ioo_subset_Icc_self)
    (isOpen_Ioo.preimage Units.continuous_val) ?_⟩
  change (3 / 2 : ℝ) ∈ Set.Ioo 1 2
  constructor <;> norm_num

theorem unitsHaar_unitsIcc_ne_zero : unitsHaar unitsIcc ≠ 0 := by
  rw [unitsHaar_apply, image_unitsIcc, invAbsVolume, Ne,
    withDensity_apply_eq_zero measurable_invAbs.coe_nnreal_ennreal]
  have h : {x : ℝ | (invAbs x : ℝ≥0∞) ≠ 0} ∩ Set.Icc 1 2 = Set.Icc 1 2 := by
    apply Set.inter_eq_right.mpr
    intro x hx
    have hx0 : x ≠ 0 := (show (0 : ℝ) < x by linarith [hx.1]).ne'
    simp [invAbs, hx0]
  rw [h, Real.volume_Icc]
  norm_num

theorem unitsHaar_unitsIcc_ne_top : unitsHaar unitsIcc ≠ ⊤ := by
  rw [unitsHaar_apply, image_unitsIcc, invAbsVolume, withDensity_apply _ measurableSet_Icc]
  apply ne_top_of_le_ne_top (b := ∫⁻ _ in Set.Icc (1 : ℝ) 2, 1)
  · rw [setLIntegral_const, Real.volume_Icc, one_mul]
    exact ENNReal.ofReal_ne_top
  · apply setLIntegral_mono measurable_const
    intro x hx
    have h1 : (1 : ℝ≥0) ≤ ‖x‖₊ := by
      rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, Real.norm_eq_abs]
      exact le_abs.mpr (Or.inl hx.1)
    have : invAbs x ≤ 1 := inv_le_one_of_one_le₀ h1
    exact_mod_cast this

instance unitsHaar_isHaarMeasure : unitsHaar.IsHaarMeasure :=
  isHaarMeasure_of_isCompact_nonempty_interior unitsHaar unitsIcc isCompact_unitsIcc
    interior_unitsIcc_nonempty unitsHaar_unitsIcc_ne_zero unitsHaar_unitsIcc_ne_top

instance unitsSecondCountable : SecondCountableTopology ℝˣ :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology

example : LocallyCompactSpace ℝˣ := inferInstance


/-! ### Quotient measures on `N₁(ℝ) \ GL₁(ℝ)` -/

/-- The homeomorphism `N₁(ℝ) \ GL₁(ℝ) ≃ ℝˣ`, `[g] ↦ det g`. -/
def quotientUnits : LeftUnipotentQuotient 0 ℝ ≃ₜ ℝˣ :=
  (Langlands.RankinSelberg.rankOneQuotientHomeomorph (F := ℝ)).trans
    (Langlands.GodementJacquet.tateScalarEquiv ℝ).symm.toHomeomorph

theorem out_eq (q : LeftUnipotentQuotient 0 ℝ) :
    q.out = Langlands.RankinSelberg.rankOneQuotientHomeomorph q := by
  have h := Langlands.RankinSelberg.rankOneQuotientHomeomorph_mk (F := ℝ) q.out
  rw [Quotient.out_eq] at h
  exact h.symm

theorem quotientUnits_symm_out (u : ℝˣ) :
    (quotientUnits.symm u).out = Langlands.GodementJacquet.tateScalarEquiv ℝ u := by
  rw [out_eq]
  exact quotientUnits.apply_symm_apply u ▸ rfl

theorem quotientUnits_mk (g : Langlands.GeneralLinear 1 ℝ) :
    quotientUnits (Quotient.mk _ g) = GeneralLinear.determinant g := rfl

theorem quotientUnits_rightTranslate (g : Langlands.GeneralLinear (0 + 1) ℝ)
    (q : LeftUnipotentQuotient 0 ℝ) :
    quotientUnits (QuotientIntegration.rightTranslate _ g q) =
      quotientUnits q * GeneralLinear.determinant g := by
  induction q using Quotient.inductionOn with
  | h x =>
    rw [QuotientIntegration.rightTranslate_mk]
    exact map_mul GeneralLinear.determinant x g

variable (D : RealQuotientMeasureData 0)

instance mapQuotientUnits_isMulLeftInvariant :
    (D.measure.map quotientUnits).IsMulLeftInvariant := by
  have := D.unipotentHaar_rightInvariant
  refine ⟨fun u => ?_⟩
  have hm : Measurable fun v : ℝˣ => u * v :=
    (show Continuous fun v : ℝˣ => u * v from continuous_const.mul continuous_id).measurable
  set g := Langlands.GodementJacquet.tateScalarEquiv ℝ u
  have hdet : GeneralLinear.determinant g = u :=
    (Langlands.GodementJacquet.tateScalarEquiv ℝ).symm_apply_apply u
  have hcomp : (fun v : ℝˣ => u * v) ∘ quotientUnits =
      quotientUnits ∘ QuotientIntegration.rightTranslate _ g := by
    funext q
    simp only [Function.comp_apply]
    rw [quotientUnits_rightTranslate, hdet, mul_comm]
  rw [map_map hm quotientUnits.continuous.measurable, hcomp,
    ← map_map quotientUnits.continuous.measurable
      (QuotientIntegration.rightTranslate _ g).continuous.measurable,
    (D.compatible.right_invariant g).map_eq]

instance mapQuotientUnits_regular : (D.measure.map quotientUnits).Regular := by
  have := D.unipotentHaar_rightInvariant
  have := D.compatible.regular
  exact Regular.map quotientUnits

/-- Every compatible quotient measure on `N₁(ℝ) \ GL₁(ℝ)` is a positive multiple of the
transported multiplicative Haar measure `|x|⁻¹ dx`. -/
theorem exists_measure_eq :
    ∃ κ : ℝ≥0, κ ≠ 0 ∧ D.measure = κ • unitsHaar.map quotientUnits.symm := by
  set κ := haarScalarFactor (D.measure.map quotientUnits) unitsHaar
  have h := isMulLeftInvariant_eq_smul (D.measure.map quotientUnits) unitsHaar
  have hD : D.measure = κ • unitsHaar.map quotientUnits.symm := by
    have h2 := congrArg (Measure.map quotientUnits.symm) h
    rw [map_map quotientUnits.symm.continuous.measurable quotientUnits.continuous.measurable,
      quotientUnits.symm_comp_self, Measure.map_id, Measure.map_smul] at h2
    · exact h2
    · exact quotientUnits.symm.continuous.measurable.aemeasurable
  have := D.unipotentHaar_rightInvariant
  refine ⟨κ, fun h0 => D.compatible.nonzero ?_, hD⟩
  rw [hD, h0, zero_smul]

/-- Extension by zero of a function on the quotient to a function on `ℝ`. -/
def unitsExtend (H : LeftUnipotentQuotient 0 ℝ → ℂ) (x : ℝ) : ℂ :=
  if h : x = 0 then 0 else H (quotientUnits.symm (Units.mk0 x h))

theorem unitsExtend_val (H : LeftUnipotentQuotient 0 ℝ → ℂ) (u : ℝˣ) :
    unitsExtend H u = H (quotientUnits.symm u) := by
  simp only [unitsExtend, u.ne_zero, ↓reduceDIte, Units.mk0_val]

variable {D}

theorem integral_eq {κ : ℝ≥0} (hκ : D.measure = κ • unitsHaar.map quotientUnits.symm)
    (H : LeftUnipotentQuotient 0 ℝ → ℂ) :
    ∫ q, H q ∂D.measure = (κ : ℂ) * ∫ x, ((|x|⁻¹ : ℝ) : ℂ) * unitsExtend H x := by
  rw [hκ, integral_smul_nnreal_measure,
    quotientUnits.symm.measurableEmbedding.integral_map H, ← integral_unitsHaar]
  rw [NNReal.smul_def, Complex.real_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  rw [unitsExtend_val]

theorem integrable_iff {κ : ℝ≥0} (hκ0 : κ ≠ 0)
    (hκ : D.measure = κ • unitsHaar.map quotientUnits.symm)
    (H : LeftUnipotentQuotient 0 ℝ → ℂ) :
    Integrable H D.measure ↔
      Integrable (fun x => ((|x|⁻¹ : ℝ) : ℂ) * unitsExtend H x) := by
  rw [hκ, ← integrable_unitsHaar_iff]
  have hsmul : (κ • unitsHaar.map quotientUnits.symm : Measure _) =
      (κ : ℝ≥0∞) • unitsHaar.map quotientUnits.symm := rfl
  rw [hsmul, integrable_smul_measure (by exact_mod_cast hκ0) ENNReal.coe_ne_top,
    quotientUnits.symm.measurableEmbedding.integrable_map_iff]
  apply integrable_congr
  filter_upwards [] with u
  rw [unitsExtend_val]
  rfl

end Langlands.Global.RankinSelbergGlobal.RealRankZero
