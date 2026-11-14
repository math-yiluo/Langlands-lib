import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalAverage
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUniformBox
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixUnfolding
/-! # Right principal averaging and uniform original-integral extraction -/

noncomputable section

open MeasureTheory Topology
open scoped NNReal ENNReal

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement RankOneCharacterReductionStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map diagonal_abs_bound diagonal_abs_last exists_rankOneCutoff exists_rankOneEmbedding_support glCoefficientModel_isOfWhittakerType isEqualRankLPolynomial_characterChange_normalized isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit matrixComparisonModelsTopology matrixComparisonPositiveBorel matrixComparisonPositiveDisconnected matrixComparisonPositiveGLBorel matrixComparisonPositiveGLMeasurable matrixComparisonPositiveLocalField matrixComparisonPositiveMeasurable matrixComparisonPositiveQuotientBorel matrixComparisonPositiveQuotientMeasurable matrixComparisonPositiveT2 matrixComparisonPositiveTopology matrixComparisonPositiveUnipotentBorel matrixComparisonPositiveUnipotentMeasurable matrixComparisonPositiveValuation normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaFactor_of_blockZero_one rankOneGammaFactor_of_normalized_blockZero_one rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rankOne_blockZero_exists_ne_zero singleton_modulus_real unequalRankCompactSupport unequalRankFiniteExpansion unequalRankGammaPropagation unequalRankIwasawaSupport unequalRankUnitSpan zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

universe uG uF

section RightAverage



end RightAverage

section SubgroupAverage


end SubgroupAverage

namespace RankOneBox
open Langlands.RankinSelberg.RankOneBox hiding ModelBoxConditions averagedModelCoefficient_eq_of_left_invariant box boxCoefficientBorelSpace boxCoefficientLocalField boxCoefficientMeasurableSpace boxCoefficientTopology boxCoefficientValuativeRel boxCoefficient_extraction_of_principalLevel boxCoefficient_mul_principalLevel boxCoefficient_point boxComparisonVolume boxConvergenceBorelSpace boxConvergenceLocalField boxConvergenceMeasurableSpace boxConvergenceSecondCountable boxConvergenceT2 boxConvergenceTopology boxConvergenceUnipotentBorel boxConvergenceUnipotentMeasurable boxConvergenceUnitsBorel boxConvergenceUnitsMeasurable boxConvergenceUnitsSecondCountable boxConvergenceValuativeRel boxEntry boxExtractionConstant boxExtractionConstant_pos boxLatticeCentre boxLatticeTest boxLatticeTest_apply boxLatticeTest_eq_compactOpenIndicator boxSupport boxVolumeBorelSpace boxVolumeLocalField boxVolumeMeasurableSpace boxVolumeTopology boxVolumeUnipotentBorel boxVolumeUnipotentMeasurable boxVolumeValuativeRel box_comparison_of_integrable box_eq_pi box_eq_rectangularLatticeCoset box_matrixIntegrand_eq_of_eq_on_box coe_unitLevel continuous_determinantWeight continuous_glModelFunction continuous_principalAverage continuous_rankOneEmbedding continuous_unipotent_entry cutoffUnipotent_mem_principalLevel determinantRankOne_point diagonalUnits_mem_principalLevel exists_box_averagedModelCoefficient_eq exists_box_constant exists_mem_principalLevel_mul_inv_upper exists_point_mul_of_mem_box glLocallyCompact glSecondCountable instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceUnitsCarrier instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceUnitsCarrier instSecondCountableTopologyCarrier instT2SpaceCarrier instT2SpaceCarrier_1 instT2SpaceCarrier_2 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 integer_of_mem_principalLevel integral_eq_of_support integral_param_of_eq inv_sub_one_mem_levelSet isCompact_box isCompact_boxEntry isCompact_unipotentBox isOpen_box isOpen_boxEntry isOpen_boxSupport isOpen_torusBox isOpen_unipotentBox isOpen_unitLevel levelSet_eq_additiveLattice lintegral_enorm_eq_of_support lintegral_param_of_eq matrixIntegrand_mul_principalLevel matrixIntegrand_point matrixLocallyCompact measurableSet_integralSubgroup measurePreserving_rshift mem_box_iff mem_box_unipotent_mul_iff mem_torusBox_of_mem_box mem_unitLevel_iff modelFunction_eq_determinantRankOne_of_mem_box mul_mem_box mul_mem_box_iff mul_mem_box_iff_of_le mul_mem_box_of_le mul_sub_one_mem_levelSet one_mem_box one_mem_boxSupport one_mem_unipotentBox parameterBase_isMulLeftInvariant point_eq_mul principalAverage principalAverageGLBorel principalAverageGLLocallyCompact principalAverageGLMeasurable principalAverageGLSecondCountable principalAverageLocalField principalAverageMatrixLocallyCompact principalAverageT2 principalAverageTopology principalAverageValuativeRel principalAverage_box_integral principalAverage_equivariant principalAverage_extraction principalAverage_mul principalAveragingMeasure principalAveragingMeasure_ae_det_norm principalAveragingMeasure_ae_mem principalAveragingMeasure_finite principalAveragingMeasure_fixed principalAveragingMeasure_integral principalAveragingMeasure_mass principalLevel_firstRow principalLevel_le_integral principalLevel_mass_pos principalMeasure_extraction rankOneEmbedding_eq_point rankOneModelValues_subset rankOneModel_convergesOnRight_of_matrix rankOne_support_of_principalLevel restrict_boxSupport_lt_top restrict_boxSupport_pos standardCharacter_eq_one tailMeasure_torusBox tailMeasure_torusBox_lt_top tailMeasure_torusBox_pos torusBox torusBox_eq_pi torusFactor_mem uniformBoxGLBorel uniformBoxGLMeasurable uniformBoxLocalField uniformBoxSecondCountable uniformBoxT2 uniformBoxTopology uniformBoxUnipotentBorel uniformBoxUnipotentMeasurable uniformBoxUnitsBorel uniformBoxUnitsMeasurable uniformBoxUnitsSecondCountable uniformBoxValuativeRel uniformBox_mul_principalLevel uniform_box_extraction unipotentBox unipotentBox_eq_entry_preimage unipotentBox_subset unipotentHaar_unipotentBox_lt_top unipotentHaar_unipotentBox_lt_top_all unipotentHaar_unipotentBox_pos unipotentLocallyCompact unipotentSecondCountable unipotent_mul_rankOne_apply unipotent_mul_rankOne_apply_zero unitLevel unitLevel_le_integralUnits unitLevel_measure_le unitLevel_measure_pos unitsSecondCountable weight_smul_integrand
open Langlands.AllField.RankinSelberg.RankOneBox
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement RankOneCharacterReductionStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map diagonal_abs_bound diagonal_abs_last exists_rankOneCutoff exists_rankOneEmbedding_support glCoefficientModel_isOfWhittakerType isEqualRankLPolynomial_characterChange_normalized isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit matrixComparisonModelsTopology matrixComparisonPositiveBorel matrixComparisonPositiveDisconnected matrixComparisonPositiveGLBorel matrixComparisonPositiveGLMeasurable matrixComparisonPositiveLocalField matrixComparisonPositiveMeasurable matrixComparisonPositiveQuotientBorel matrixComparisonPositiveQuotientMeasurable matrixComparisonPositiveT2 matrixComparisonPositiveTopology matrixComparisonPositiveUnipotentBorel matrixComparisonPositiveUnipotentMeasurable matrixComparisonPositiveValuation normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaFactor_of_blockZero_one rankOneGammaFactor_of_normalized_blockZero_one rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rankOne_blockZero_exists_ne_zero singleton_modulus_real unequalRankCompactSupport unequalRankFiniteExpansion unequalRankGammaPropagation unequalRankIwasawaSupport unequalRankUnitSpan zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement isClopen_rectangularLatticeCoset isCompact_rectangularLatticeCoset mem_rectangularLatticeCoset padicLatticeGeometry padicRectangularHaarScaling padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists rectangularLatticeCoset rectangularLatticeCosetTest rectangularLatticeCosetTest_apply
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.Conductor
open Langlands.RankinSelberg.RankOneIwasawa hiding ColBound abv_det_eq_one ae_outerMeasure_mem colBound_of_inv colBound_zero congruenceGroup congruenceGroup_le_integral conj_mem_congruenceGroup continuous_det_units continuous_point continuous_torusCoord continuous_torusModulus continuous_weight det_point det_unipotent_mul determinantWeight_diagPoint diagPoint elemUnipotent elemUnipotent_val exists_congruenceGroup_le exists_cornerSchwartz exists_lattice_nontrivial exists_lattice_subset exists_mem_lattice exists_mem_matLattice exists_ne_zero_of_unipotentTransform_ne_zero exists_schwartz_congruence glLocallyCompact glLocallyCompactU glOneMeasure glOneMeasure_sigmaFinite glSecondCountable glSecondCountableU instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_1 instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_2 instBorelSpaceUnitsCarrier instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instIsNonarchimedeanLocalFieldCarrier_3 instIsNonarchimedeanLocalFieldCarrier_4 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_1 instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_2 instMeasurableSpaceUnitsCarrier instMeasurableSpaceUnitsCarrier_1 instSecondCountableTopologyCarrier instSecondCountableTopologyCarrier_1 instT2SpaceCarrier instT2SpaceCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instTopologicalSpaceCarrier_3 instTopologicalSpaceCarrier_4 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 instValuativeRelCarrier_3 instValuativeRelCarrier_4 integralSet integralSubgroup_mem_matLattice integral_matrixIntegrand_unfold integral_mul_matLattice inv_mem_lattice_of_notMem inv_mem_of_colBound isCompact_lattice isOpen_congruenceGroup isOpen_lattice isOpen_matLattice iwasawaMeasure iwasawaMeasure_point_preimage iwasawaMeasure_sFinite lattice_mono lattice_mul map_iwasawaMeasure_prod map_unfoldedMeasure matLattice matLattice_basis matLattice_mono matLattice_mul matLattice_mul_integral matrixIntegrand_unfoldedPoint matrixLocallyCompact matrixLocallyCompactU measurable_point measurable_unfoldedPoint measurePreserving_shift mem_lattice_zero_iff mem_matLattice mem_matLattice_of_support mul_sub_one_mem one_add_mem_lattice_zero one_add_single_apply one_mem_lattice_zero outerMeasure outerMeasure_sFinite parameterBase_isMulLeftInvariant parameterMeasure parameterMeasure_eq_prod parameterMeasure_sigmaFinite schwartzOfLattice schwartzOfLattice_apply schwartz_invariance schwartz_support_bound standardCharacter_elemUnipotent tailMeasure tailMeasure_sigmaFinite torusModulus torusModulus_apply torusModulus_cons_one torusModulus_eq_one unfoldedMeasure unfoldedMeasure_eq unfoldedPoint unfoldedPoint_eq unipotentConj_map unipotentLocallyCompact unipotentLocallyCompactU unipotentSecondCountable unipotentSecondCountableU unipotentTransform unipotentTransform_diag_bounds unipotentTransform_eq_zero_of_shift unipotentTransform_mul_right unipotent_col_zero unipotent_mul_single_zero unitsSecondCountable weight weight_apply weight_glOne weight_split
open Langlands.AllField.RankinSelberg.RankOneIwasawa
open Langlands.RankinSelberg.UnequalRankMirabolicUnitTest

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance principalAverageT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance principalAverageGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance principalAverageGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance principalAverageGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology n
local instance principalAverageMatrixLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Matrix (Fin n) (Fin n) F) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → F))
local instance principalAverageGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear n F) := inferInstance

variable {n : ℕ}

/-- The actual normalized right average over the principal subgroup. -/
def principalAverage (a : ℕ) (H : Langlands.GeneralLinear (n + 1) F → ℂ) :
    Langlands.GeneralLinear (n + 1) F → ℂ :=
  normalizedRightAverage (generalLinearHaar F n)
    (principalLevelSubgroup F n a) H

theorem continuous_principalAverage (a : ℕ)
    {H : Langlands.GeneralLinear (n + 1) F → ℂ} (hH : Continuous H) :
    Continuous (principalAverage F a H) := by
  change Continuous (fun g => _ * ∫ k in
    (principalLevelSubgroup F n a : Set _), H (g * k) ∂generalLinearHaar F n)
  apply Continuous.const_mul
  exact continuous_parametric_integral_of_continuous (f := fun g k => H (g * k))
    (hH.comp (continuous_fst.mul continuous_snd))
    (isCompact_principalLevelOpenSubgroup F n a)

theorem principalAverage_mul (a : ℕ)
    (H : Langlands.GeneralLinear (n + 1) F → ℂ)
    {k : Langlands.GeneralLinear (n + 1) F}
    (hk : k ∈ principalLevelSubgroup F n a) (g) :
    principalAverage F a H (g * k) = principalAverage F a H g :=
  normalizedRightAverage_mul_subgroup _ _ (principalLevelOpenSubgroup F n a).isOpen.measurableSet H hk g

theorem principalAverage_equivariant (ψ : UnitaryAdditiveCharacter F) (a : ℕ)
    (H : Langlands.GeneralLinear (n + 1) F → ℂ)
    (heq : ∀ u : upperUnipotent (n + 1) F, ∀ h,
      H (u.val * h) = (standardCharacter ψ n u : ℂ) * H h)
    (u : upperUnipotent (n + 1) F) (g) :
    principalAverage F a H (u.val * g) =
      (standardCharacter ψ n u : ℂ) * principalAverage F a H g := by
  simp only [principalAverage, normalizedRightAverage, mul_assoc, heq, integral_const_mul]
  ring

/-- The same fixed box is right invariant on the entire matrix space. -/
theorem uniformBox_mul_principalLevel (q : ℤ) (a : ℕ)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    {k : Langlands.GeneralLinear (n + 1) F}
    (hk : k ∈ principalLevelSubgroup F n a) :
    boxLatticeTest F (q + a) q a (X * k.val) = boxLatticeTest F (q + a) q a X := by
  have hb := mul_mem_box_iff_of_le F (show q ≤ q + a by omega)
    (fun _ hy => principalLevel_firstRow F q a hy) X hk
  simp only [boxLatticeTest_apply]
  by_cases hX : X ∈ box F (q + a) q a <;> simp [hb, hX]

/-- Any convergent original box integral is preserved by principal averaging. -/
theorem principalAverage_box_integral (q : ℤ) (a : ℕ)
    (H : Langlands.GeneralLinear (n + 1) F → ℂ)
    (hconv : Integrable (fun g => boxLatticeTest F (q + a) q a g.val * H g)
      (generalLinearHaar F n)) :
    Integrable (fun g => boxLatticeTest F (q + a) q a g.val * principalAverage F a H g)
      (generalLinearHaar F n) ∧
    ∫ g, boxLatticeTest F (q + a) q a g.val * principalAverage F a H g
      ∂generalLinearHaar F n =
        ∫ g, boxLatticeTest F (q + a) q a g.val * H g
          ∂generalLinearHaar F n := by
  let K := principalLevelOpenSubgroup F n a
  exact normalizedRightAverage_integral (generalLinearHaar F n)
    (K : Set _) K.isOpen.measurableSet
    (isCompact_principalLevelOpenSubgroup F n a).measure_lt_top.ne
    (K.isOpen.measure_pos (generalLinearHaar F n) ⟨1, K.one_mem⟩).ne'
    (fun g => boxLatticeTest F (q + a) q a g.val) H
    (fun k hk g => uniformBox_mul_principalLevel F q a g.val hk) hconv

/-- One fixed box and right averaging extract every continuous equivariant H.
Only the original-to-averaged direction of convergence is asserted. -/
theorem principalAverage_extraction (ψ : UnitaryAdditiveCharacter F)
    {m : ℕ} {a : ℕ} (ha : 0 < a)
    (hA : 0 ≤ (⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
    (H : Langlands.GeneralLinear (m + 1 + 1) F → ℂ) (hH : Continuous H)
    (heq : ∀ u : upperUnipotent (m + 1 + 1) F, ∀ h,
      H (u.val * h) = (standardCharacter ψ (m + 1) u : ℂ) * H h)
    (hconv : Integrable (fun h =>
      boxLatticeTest F ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
        ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a h.val * H h)
      (generalLinearHaar F (m + 1))) :
    Integrable (fun g => principalAverage F a H (rankOneEmbedding m g))
      (glOneMeasure F (m + 1)) ∧
    ∫ h, boxLatticeTest F ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
        ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a h.val * H h
        ∂generalLinearHaar F (m + 1) =
      (boxExtractionConstant F (n := m + 1)
        ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
        ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a : ℂ) *
        ∫ g, principalAverage F a H (rankOneEmbedding m g) ∂glOneMeasure F (m + 1) := by
  obtain ⟨hc, hv⟩ := principalAverage_box_integral F _ a H hconv
  obtain ⟨hiff, he⟩ := uniform_box_extraction F ψ ha hA (principalAverage F a H)
    (continuous_principalAverage F a hH)
    (principalAverage_equivariant F ψ a H heq) (fun _ hk g => principalAverage_mul F a H hk g)
  exact ⟨hiff.1 hc, hv.symm.trans he⟩

/-- The principal subgroup has finite, strictly positive Haar mass. -/
theorem principalLevel_mass_pos (a : ℕ) :
    0 < (generalLinearHaar F n).real
      (principalLevelSubgroup F n a : Set _) := by
  apply ENNReal.toReal_pos
  · exact ((principalLevelOpenSubgroup F n a).isOpen.measure_pos _
      ⟨1, (principalLevelSubgroup F n a).one_mem⟩).ne'
  · exact (isCompact_principalLevelOpenSubgroup F n a).measure_lt_top.ne

/-- A positive scalar multiple of normalized Haar on the actual principal
subgroup. Its total mass is C rather than one. -/
def principalAveragingMeasure (a : ℕ) (C : ℝ) :
    Measure (Langlands.GeneralLinear (n + 1) F) :=
  ENNReal.ofReal (C / (generalLinearHaar F n).real
    (principalLevelSubgroup F n a : Set _)) •
      (generalLinearHaar F n).restrict (principalLevelSubgroup F n a)

instance principalAveragingMeasure_finite (a : ℕ) (C : ℝ) :
    IsFiniteMeasure (principalAveragingMeasure F (n := n) a C) := by
  have : IsFiniteMeasure ((generalLinearHaar F n).restrict
      (principalLevelSubgroup F n a : Set _)) :=
    isFiniteMeasure_restrict.mpr
      (isCompact_principalLevelOpenSubgroup F n a).measure_lt_top.ne
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top

theorem principalAveragingMeasure_ae_mem (a : ℕ) (C : ℝ) :
    ∀ᵐ k ∂principalAveragingMeasure F (n := n) a C,
      k ∈ principalLevelSubgroup F n a :=
  Measure.ae_smul_measure
    (ae_restrict_mem (principalLevelOpenSubgroup F n a).isOpen.measurableSet) _

theorem principalAveragingMeasure_ae_det_norm (a : ℕ) (C : ℝ) :
    ∀ᵐ k ∂principalAveragingMeasure F (n := n) a C,
      normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) (Matrix.det k.val) = 1 := by
  filter_upwards [principalAveragingMeasure_ae_mem F a C] with k hk
  exact abv_det_eq_one F (principalLevel_le_integral F a hk)

theorem principalAveragingMeasure_integral (a : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (H : Langlands.GeneralLinear (n + 1) F → ℂ) (g) :
    ∫ k, H (g * k) ∂principalAveragingMeasure F a C =
      (C : ℂ) * principalAverage F a H g := by
  rw [principalAveragingMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (div_nonneg hC (principalLevel_mass_pos F a).le)]
  simp only [principalAverage, normalizedRightAverage, Complex.real_smul, Complex.ofReal_div]
  ring

theorem principalAveragingMeasure_mass (a : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    principalAveragingMeasure F (n := n) a C Set.univ = ENNReal.ofReal C := by
  have hp := principalLevel_mass_pos F (n := n) a
  have hf : generalLinearHaar F n
      (principalLevelSubgroup F n a : Set _) ≠ ⊤ :=
    (isCompact_principalLevelOpenSubgroup F n a).measure_lt_top.ne
  simp only [principalAveragingMeasure, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul]
  calc
    _ = ENNReal.ofReal (C / (generalLinearHaar F n).real
        (principalLevelSubgroup F n a : Set _)) *
        ENNReal.ofReal ((generalLinearHaar F n).real
          (principalLevelSubgroup F n a : Set _)) := by
      rw [measureReal_def, ENNReal.ofReal_toReal hf]
    _ = ENNReal.ofReal C := by
      rw [← ENNReal.ofReal_mul (div_nonneg hC hp.le), div_mul_cancel₀ _ hp.ne']

/-- A principal fixed original function is multiplied by exactly C. -/
theorem principalAveragingMeasure_fixed (a : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (H : Langlands.GeneralLinear (n + 1) F → ℂ)
    (hH : ∀ k ∈ principalLevelSubgroup F n a, ∀ g, H (g * k) = H g)
    (g) :
    ∫ k, H (g * k) ∂principalAveragingMeasure F a C = (C : ℂ) * H g := by
  calc
    _ = ∫ _k, H g ∂principalAveragingMeasure F a C := by
      apply integral_congr_ae
      filter_upwards [principalAveragingMeasure_ae_mem F a C] with k hk
      exact hH k hk g
    _ = (C : ℂ) * H g := by
      simp [integral_const, measureReal_def, principalAveragingMeasure_mass F a hC,
        ENNReal.toReal_ofReal hC, Complex.real_smul]

/-- The fixed box extracts the actual compact principal measure average for
every continuous left equivariant function with convergent original integrand. -/
theorem principalMeasure_extraction (ψ : UnitaryAdditiveCharacter F)
    {m : ℕ} {a : ℕ} (ha : 0 < a)
    (hA : 0 ≤ (⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
    (H : Langlands.GeneralLinear (m + 1 + 1) F → ℂ) (hH : Continuous H)
    (heq : ∀ u : upperUnipotent (m + 1 + 1) F, ∀ h,
      H (u.val * h) = (standardCharacter ψ (m + 1) u : ℂ) * H h)
    (hconv : Integrable (fun h =>
      boxLatticeTest F ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
        ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a h.val * H h)
      (generalLinearHaar F (m + 1))) :
    let C := boxExtractionConstant F (n := m + 1)
      ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
      ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a
    let μ := principalAveragingMeasure F (n := m + 1) a C
    Integrable (fun g => ∫ k, H (rankOneEmbedding m g * k) ∂μ)
        (glOneMeasure F (m + 1)) ∧
      ∫ h, boxLatticeTest F ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
          ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a h.val * H h
          ∂generalLinearHaar F (m + 1) =
        ∫ g, ∫ k, H (rankOneEmbedding m g * k) ∂μ ∂glOneMeasure F (m + 1) := by
  dsimp only
  have hC := (boxExtractionConstant_pos F (n := m + 1)
    (q := (⟨⟩ : LocalFieldData F).additiveConductor ψ) hA ha).le
  simp_rw [principalAveragingMeasure_integral F a hC]
  obtain ⟨hc, hv⟩ := principalAverage_extraction F ψ ha hA H hH heq hconv
  exact ⟨hc.const_mul _, by rw [integral_const_mul]; exact hv⟩

end RankOneBox

end Langlands.AllField.RankinSelberg
