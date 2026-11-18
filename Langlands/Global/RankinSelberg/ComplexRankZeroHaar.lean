import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.Representation.GodementJacquet.TateScalarTransport
import Langlands.Representation.RankinSelberg.RankOneQuotient
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.RingTheory.Complex
import Mathlib.Analysis.Normed.Ring.Units

/-! # The quotient measure on `N₁(ℂ) \ GL₁(ℂ)`

At rank one the unipotent subgroup is trivial, and the quotient `N₁(ℂ) \ GL₁(ℂ)` is
homeomorphic to `ℂˣ`. Every compatible quotient measure is a positive multiple of the
multiplicative Haar measure `|z|⁻² dz` (`dz` Lebesgue measure on `ℂ`). See the paired Markdown.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology
open scoped NNReal ENNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexRankZero

open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal

/-- Borel structure on `ℂˣ`. -/
local instance unitsMeasurable : MeasurableSpace ℂˣ := borel _
local instance unitsBorel : BorelSpace ℂˣ := ⟨rfl⟩

local instance rankZeroGLMeasurable : MeasurableSpace (Langlands.GeneralLinear (0 + 1) ℂ) :=
  borel _
local instance rankZeroGLBorel : BorelSpace (Langlands.GeneralLinear (0 + 1) ℂ) := ⟨rfl⟩
local instance rankZeroNMeasurable :
    MeasurableSpace (GeneralLinear.upperUnipotent (0 + 1) ℂ) := borel _
local instance rankZeroNBorel : BorelSpace (GeneralLinear.upperUnipotent (0 + 1) ℂ) := ⟨rfl⟩
local instance rankZeroQMeasurable : MeasurableSpace (LeftUnipotentQuotient 0 ℂ) := borel _
local instance rankZeroQBorel : BorelSpace (LeftUnipotentQuotient 0 ℂ) := ⟨rfl⟩

/-! ### The measure `|z|⁻² dz` on `ℂ` and on `ℂˣ` -/

/-- The density `|z|⁻²`, with value `0` at `z = 0`. -/
def invNormSq (z : ℂ) : ℝ≥0 := (‖z‖₊ ^ 2)⁻¹

theorem measurable_invNormSq : Measurable invNormSq :=
  (measurable_nnnorm.pow_const 2).inv

/-- The measure `|z|⁻² dz` on `ℂ`. -/
def invNormSqVolume : Measure ℂ := volume.withDensity fun z => (invNormSq z : ℝ≥0∞)

theorem invNormSqVolume_singleton_zero : invNormSqVolume {0} = 0 := by
  rw [invNormSqVolume, withDensity_apply _ (measurableSet_singleton 0)]
  simp

theorem measurableEmbedding_val : MeasurableEmbedding (Units.val : ℂˣ → ℂ) :=
  Units.isOpenEmbedding_val.measurableEmbedding

/-- The multiplicative Haar measure `|z|⁻² dz` on `ℂˣ`. -/
def unitsHaar : Measure ℂˣ := invNormSqVolume.comap Units.val

theorem range_val : Set.range (Units.val : ℂˣ → ℂ) = {0}ᶜ := by
  ext x
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, rfl⟩
    exact u.ne_zero
  · intro hx
    exact ⟨Units.mk0 x hx, rfl⟩

theorem map_val_unitsHaar : unitsHaar.map Units.val = invNormSqVolume := by
  rw [unitsHaar, measurableEmbedding_val.map_comap, range_val]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  simpa using invNormSqVolume_singleton_zero

/-- Integration against `unitsHaar` is integration against `|z|⁻² dz`. -/
theorem integral_unitsHaar (G : ℂ → ℂ) :
    ∫ u, G u ∂unitsHaar = ∫ z, (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * G z := by
  have h := measurableEmbedding_val.integral_map (μ := unitsHaar) G
  rw [map_val_unitsHaar] at h
  rw [← h, invNormSqVolume, integral_withDensity_eq_integral_smul measurable_invNormSq]
  congr 1

theorem integrable_unitsHaar_iff (G : ℂ → ℂ) :
    Integrable (fun u : ℂˣ => G u) unitsHaar ↔
      Integrable (fun z => (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * G z) := by
  have h := measurableEmbedding_val.integrable_map_iff (μ := unitsHaar) (g := G)
  rw [map_val_unitsHaar] at h
  rw [← Function.comp_def, ← h, invNormSqVolume,
    integrable_withDensity_iff_integrable_smul measurable_invNormSq]
  apply integrable_congr
  filter_upwards [] with z
  rw [NNReal.smul_def, Complex.real_smul]
  simp [invNormSq]

/-- Lebesgue measure under `z ↦ c z`: the real determinant of multiplication by `c` is
`|c|²`. -/
theorem map_volume_mul_left {c : ℂ} (hc : c ≠ 0) :
    Measure.map (fun z : ℂ => c * z) volume = ENNReal.ofReal ((‖c‖ ^ 2)⁻¹) • volume := by
  have hdet : LinearMap.det (Algebra.lmul ℝ ℂ c) = ‖c‖ ^ 2 := by
    rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  have hpos : 0 < ‖c‖ ^ 2 := pow_pos (norm_pos_iff.mpr hc) 2
  have hne : LinearMap.det (Algebra.lmul ℝ ℂ c) ≠ 0 := by
    rw [hdet]
    exact hpos.ne'
  have h := map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ) hne
  rw [hdet, abs_of_pos (inv_pos.mpr hpos)] at h
  have hf : (⇑(Algebra.lmul ℝ ℂ c : ℂ →ₗ[ℝ] ℂ)) = fun z => c * z := by
    funext z
    simp
  rw [hf] at h
  exact h

/-- Dilation invariance of `|z|⁻² dz`. -/
theorem invNormSqVolume_preimage_mul {c : ℂ} (hc : c ≠ 0) {T : Set ℂ} (hT : MeasurableSet T) :
    invNormSqVolume ((fun z => c * z) ⁻¹' T) = invNormSqVolume T := by
  have hmul : Measurable fun z : ℂ => c * z := measurable_const_mul c
  rw [invNormSqVolume, withDensity_apply _ (hmul hT), withDensity_apply _ hT,
    ← lintegral_indicator (hmul hT), ← lintegral_indicator hT]
  set k : ℝ≥0∞ := ((‖c‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) with hk_def
  set G : ℂ → ℝ≥0∞ := T.indicator fun y => (invNormSq y : ℝ≥0∞) * k with hG
  have hGm : Measurable G :=
    (((measurable_invNormSq).coe_nnreal_ennreal).mul_const _).indicator hT
  have hc2 : (‖c‖₊ ^ 2 : ℝ≥0) ≠ 0 := pow_ne_zero 2 (nnnorm_ne_zero_iff.mpr hc)
  have hcomp : ((fun z => c * z) ⁻¹' T).indicator (fun z => (invNormSq z : ℝ≥0∞)) =
      fun z => G (c * z) := by
    funext z
    by_cases hz : c * z ∈ T
    · have hz' : z ∈ (fun z => c * z) ⁻¹' T := hz
      rw [Set.indicator_of_mem hz', hG, Set.indicator_of_mem hz, hk_def, ← ENNReal.coe_mul]
      congr 1
      simp only [invNormSq, nnnorm_mul, mul_pow, mul_inv]
      rw [mul_comm ((‖c‖₊ ^ 2)⁻¹), mul_assoc, inv_mul_cancel₀ hc2, mul_one]
    · have hz' : z ∉ (fun z => c * z) ⁻¹' T := hz
      rw [Set.indicator_of_notMem hz', hG, Set.indicator_of_notMem hz]
  have hGeq : G = fun y => T.indicator (fun y => (invNormSq y : ℝ≥0∞)) y * k := by
    funext y
    by_cases hy : y ∈ T <;> simp [hG, hy]
  have hk : ENNReal.ofReal ((‖c‖ ^ 2)⁻¹) * k = 1 := by
    have h1 : ENNReal.ofReal ((‖c‖ ^ 2)⁻¹) = (((‖c‖₊ ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
    rw [h1, hk_def, ← ENNReal.coe_mul, inv_mul_cancel₀ hc2, ENNReal.coe_one]
  rw [hcomp, ← lintegral_map hGm hmul, map_volume_mul_left hc, lintegral_smul_measure,
    hGeq, lintegral_mul_const _ ((measurable_invNormSq.coe_nnreal_ennreal).indicator hT),
    smul_eq_mul, mul_comm, mul_assoc, mul_comm k, hk, mul_one]

/-! ### `unitsHaar` is a Haar measure on `ℂˣ` -/

theorem unitsHaar_apply (S : Set ℂˣ) : unitsHaar S = invNormSqVolume (Units.val '' S) :=
  measurableEmbedding_val.comap_apply _ S

theorem image_val_preimage_mul (g : ℂˣ) (S : Set ℂˣ) :
    Units.val '' ((fun u => g * u) ⁻¹' S) =
      (fun z : ℂ => (g : ℂ) * z) ⁻¹' (Units.val '' S) := by
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
  have hm : Measurable fun u : ℂˣ => g * u :=
    (show Continuous fun u : ℂˣ => g * u from continuous_const.mul continuous_id).measurable
  rw [map_apply hm hS, unitsHaar_apply, unitsHaar_apply,
    image_val_preimage_mul, invNormSqVolume_preimage_mul g.ne_zero
      (measurableEmbedding_val.measurableSet_image.mpr hS)]

/-- The closed annulus `1 ≤ |z| ≤ 2` in `ℂ`. -/
def closedAnnulus : Set ℂ := {z | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2}

/-- The open annulus `1 < |z| < 2` in `ℂ`. -/
def openAnnulus : Set ℂ := {z | 1 < ‖z‖ ∧ ‖z‖ < 2}

theorem openAnnulus_subset : openAnnulus ⊆ closedAnnulus :=
  fun _ hz => ⟨hz.1.le, hz.2.le⟩

theorem isOpen_openAnnulus : IsOpen openAnnulus :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem isClosed_closedAnnulus : IsClosed closedAnnulus :=
  (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)

theorem isCompact_closedAnnulus : IsCompact closedAnnulus :=
  (isCompact_closedBall (0 : ℂ) 2).of_isClosed_subset isClosed_closedAnnulus
    (fun z hz => by simpa using hz.2)

theorem three_halves_mem_openAnnulus : ((3 / 2 : ℝ) : ℂ) ∈ openAnnulus := by
  change 1 < ‖((3 / 2 : ℝ) : ℂ)‖ ∧ ‖((3 / 2 : ℝ) : ℂ)‖ < 2
  rw [Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
  constructor <;> norm_num

theorem ne_zero_of_mem_closedAnnulus {z : ℂ} (hz : z ∈ closedAnnulus) : z ≠ 0 := by
  rintro rfl
  have h := hz.1
  simp at h
  linarith

/-- The compact set of units with absolute value in `[1, 2]`. -/
def unitsAnnulus : Set ℂˣ := Units.val ⁻¹' closedAnnulus

theorem image_unitsAnnulus : Units.val '' unitsAnnulus = closedAnnulus := by
  rw [unitsAnnulus, Set.image_preimage_eq_inter_range, range_val]
  apply Set.inter_eq_left.mpr
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  exact ne_zero_of_mem_closedAnnulus hz

theorem isCompact_unitsAnnulus : IsCompact unitsAnnulus := by
  rw [Units.isOpenEmbedding_val.isInducing.isCompact_iff, image_unitsAnnulus]
  exact isCompact_closedAnnulus

theorem interior_unitsAnnulus_nonempty : (interior unitsAnnulus).Nonempty := by
  have h0 : ((3 / 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    norm_num
  exact ⟨Units.mk0 _ h0, interior_maximal (Set.preimage_mono openAnnulus_subset)
    (isOpen_openAnnulus.preimage Units.continuous_val) three_halves_mem_openAnnulus⟩

theorem unitsHaar_unitsAnnulus_ne_zero : unitsHaar unitsAnnulus ≠ 0 := by
  rw [unitsHaar_apply, image_unitsAnnulus, invNormSqVolume, Ne,
    withDensity_apply_eq_zero measurable_invNormSq.coe_nnreal_ennreal]
  have h : {z : ℂ | (invNormSq z : ℝ≥0∞) ≠ 0} ∩ closedAnnulus = closedAnnulus := by
    apply Set.inter_eq_right.mpr
    intro z hz
    have hz0 := ne_zero_of_mem_closedAnnulus hz
    simp [invNormSq, hz0]
  rw [h]
  intro h0
  exact isOpen_openAnnulus.measure_ne_zero volume ⟨_, three_halves_mem_openAnnulus⟩
    (measure_mono_null openAnnulus_subset h0)

theorem unitsHaar_unitsAnnulus_ne_top : unitsHaar unitsAnnulus ≠ ⊤ := by
  rw [unitsHaar_apply, image_unitsAnnulus, invNormSqVolume,
    withDensity_apply _ isClosed_closedAnnulus.measurableSet]
  apply ne_top_of_le_ne_top (b := ∫⁻ _ in closedAnnulus, 1)
  · rw [setLIntegral_const, one_mul]
    exact isCompact_closedAnnulus.measure_lt_top.ne
  · apply setLIntegral_mono measurable_const
    intro z hz
    have h1 : (1 : ℝ≥0) ≤ ‖z‖₊ := by
      rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
      exact hz.1
    have : invNormSq z ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h1)
    exact_mod_cast this

instance unitsHaar_isHaarMeasure : unitsHaar.IsHaarMeasure :=
  isHaarMeasure_of_isCompact_nonempty_interior unitsHaar unitsAnnulus isCompact_unitsAnnulus
    interior_unitsAnnulus_nonempty unitsHaar_unitsAnnulus_ne_zero unitsHaar_unitsAnnulus_ne_top

instance unitsSecondCountable : SecondCountableTopology ℂˣ :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology

/-! ### Quotient measures on `N₁(ℂ) \ GL₁(ℂ)` -/

/-- The homeomorphism `N₁(ℂ) \ GL₁(ℂ) ≃ ℂˣ`, `[g] ↦ det g`. -/
def quotientUnits : LeftUnipotentQuotient 0 ℂ ≃ₜ ℂˣ :=
  (Langlands.RankinSelberg.rankOneQuotientHomeomorph (F := ℂ)).trans
    (Langlands.GodementJacquet.tateScalarEquiv ℂ).symm.toHomeomorph

theorem out_eq (q : LeftUnipotentQuotient 0 ℂ) :
    q.out = Langlands.RankinSelberg.rankOneQuotientHomeomorph q := by
  have h := Langlands.RankinSelberg.rankOneQuotientHomeomorph_mk (F := ℂ) q.out
  rw [Quotient.out_eq] at h
  exact h.symm

theorem quotientUnits_symm_out (u : ℂˣ) :
    (quotientUnits.symm u).out = Langlands.GodementJacquet.tateScalarEquiv ℂ u := by
  rw [out_eq]
  exact quotientUnits.apply_symm_apply u ▸ rfl

theorem quotientUnits_mk (g : Langlands.GeneralLinear 1 ℂ) :
    quotientUnits (Quotient.mk _ g) = GeneralLinear.determinant g := rfl

theorem quotientUnits_rightTranslate (g : Langlands.GeneralLinear (0 + 1) ℂ)
    (q : LeftUnipotentQuotient 0 ℂ) :
    quotientUnits (QuotientIntegration.rightTranslate _ g q) =
      quotientUnits q * GeneralLinear.determinant g := by
  induction q using Quotient.inductionOn with
  | h x =>
    rw [QuotientIntegration.rightTranslate_mk]
    exact map_mul GeneralLinear.determinant x g

variable (D : ComplexQuotientMeasureData 0)

instance mapQuotientUnits_isMulLeftInvariant :
    (D.measure.map quotientUnits).IsMulLeftInvariant := by
  have := D.unipotentHaar_rightInvariant
  refine ⟨fun u => ?_⟩
  have hm : Measurable fun v : ℂˣ => u * v :=
    (show Continuous fun v : ℂˣ => u * v from continuous_const.mul continuous_id).measurable
  set g := Langlands.GodementJacquet.tateScalarEquiv ℂ u
  have hdet : GeneralLinear.determinant g = u :=
    (Langlands.GodementJacquet.tateScalarEquiv ℂ).symm_apply_apply u
  have hcomp : (fun v : ℂˣ => u * v) ∘ quotientUnits =
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

/-- Every compatible quotient measure on `N₁(ℂ) \ GL₁(ℂ)` is a positive multiple of the
transported multiplicative Haar measure `|z|⁻² dz`. -/
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

/-- Extension by zero of a function on the quotient to a function on `ℂ`. -/
def unitsExtend (H : LeftUnipotentQuotient 0 ℂ → ℂ) (z : ℂ) : ℂ :=
  if h : z = 0 then 0 else H (quotientUnits.symm (Units.mk0 z h))

theorem unitsExtend_val (H : LeftUnipotentQuotient 0 ℂ → ℂ) (u : ℂˣ) :
    unitsExtend H u = H (quotientUnits.symm u) := by
  simp only [unitsExtend, u.ne_zero, ↓reduceDIte, Units.mk0_val]

variable {D}

theorem integral_eq {κ : ℝ≥0} (hκ : D.measure = κ • unitsHaar.map quotientUnits.symm)
    (H : LeftUnipotentQuotient 0 ℂ → ℂ) :
    ∫ q, H q ∂D.measure = (κ : ℂ) * ∫ z, (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * unitsExtend H z := by
  rw [hκ, integral_smul_nnreal_measure,
    quotientUnits.symm.measurableEmbedding.integral_map H, ← integral_unitsHaar]
  rw [NNReal.smul_def, Complex.real_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  rw [unitsExtend_val]

theorem integrable_iff {κ : ℝ≥0} (hκ0 : κ ≠ 0)
    (hκ : D.measure = κ • unitsHaar.map quotientUnits.symm)
    (H : LeftUnipotentQuotient 0 ℂ → ℂ) :
    Integrable H D.measure ↔
      Integrable (fun z => (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * unitsExtend H z) := by
  rw [hκ, ← integrable_unitsHaar_iff]
  have hsmul : (κ • unitsHaar.map quotientUnits.symm : Measure _) =
      (κ : ℝ≥0∞) • unitsHaar.map quotientUnits.symm := rfl
  rw [hsmul, integrable_smul_measure (by exact_mod_cast hκ0) ENNReal.coe_ne_top,
    quotientUnits.symm.measurableEmbedding.integrable_map_iff]
  apply integrable_congr
  filter_upwards [] with u
  rw [unitsExtend_val]
  rfl

end Langlands.Global.RankinSelbergGlobal.ComplexRankZero
