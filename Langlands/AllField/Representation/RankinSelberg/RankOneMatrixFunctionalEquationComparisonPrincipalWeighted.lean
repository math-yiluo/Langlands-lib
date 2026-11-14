import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalWeighted
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalAverage
/-! # Spectral weights in principal compact-measure extraction -/

noncomputable section

open MeasureTheory Topology
open scoped NNReal ENNReal

namespace Langlands.AllField.RankinSelberg.RankOneBox
open Langlands.RankinSelberg.RankOneBox hiding ModelBoxConditions averagedModelCoefficient_eq_of_left_invariant box boxCoefficientBorelSpace boxCoefficientLocalField boxCoefficientMeasurableSpace boxCoefficientTopology boxCoefficientValuativeRel boxCoefficient_extraction_of_principalLevel boxCoefficient_mul_principalLevel boxCoefficient_point boxComparisonVolume boxConvergenceBorelSpace boxConvergenceLocalField boxConvergenceMeasurableSpace boxConvergenceSecondCountable boxConvergenceT2 boxConvergenceTopology boxConvergenceUnipotentBorel boxConvergenceUnipotentMeasurable boxConvergenceUnitsBorel boxConvergenceUnitsMeasurable boxConvergenceUnitsSecondCountable boxConvergenceValuativeRel boxEntry boxExtractionConstant boxExtractionConstant_pos boxLatticeCentre boxLatticeTest boxLatticeTest_apply boxLatticeTest_eq_compactOpenIndicator boxSupport boxVolumeBorelSpace boxVolumeLocalField boxVolumeMeasurableSpace boxVolumeTopology boxVolumeUnipotentBorel boxVolumeUnipotentMeasurable boxVolumeValuativeRel box_comparison_of_integrable box_eq_pi box_eq_rectangularLatticeCoset box_matrixIntegrand_eq_of_eq_on_box coe_unitLevel continuous_determinantWeight continuous_glModelFunction continuous_principalAverage continuous_rankOneEmbedding continuous_unipotent_entry cutoffUnipotent_mem_principalLevel determinantRankOne_point determinantWeight_mul_of_norm_one determinantWeight_rankOneEmbedding determinantWeighted_equivariant diagonalUnits_mem_principalLevel exists_box_averagedModelCoefficient_eq exists_box_constant exists_mem_principalLevel_mul_inv_upper exists_point_mul_of_mem_box glLocallyCompact glSecondCountable instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceUnitsCarrier instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceUnitsCarrier instSecondCountableTopologyCarrier instT2SpaceCarrier instT2SpaceCarrier_1 instT2SpaceCarrier_2 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 integer_of_mem_principalLevel integral_eq_of_support integral_param_of_eq inv_sub_one_mem_levelSet isCompact_box isCompact_boxEntry isCompact_unipotentBox isOpen_box isOpen_boxEntry isOpen_boxSupport isOpen_torusBox isOpen_unipotentBox isOpen_unitLevel levelSet_eq_additiveLattice lintegral_enorm_eq_of_support lintegral_param_of_eq matrixIntegrand_mul_principalLevel matrixIntegrand_point matrixLocallyCompact measurableSet_integralSubgroup measurePreserving_rshift mem_box_iff mem_box_unipotent_mul_iff mem_torusBox_of_mem_box mem_unitLevel_iff modelFunction_eq_determinantRankOne_of_mem_box mul_mem_box mul_mem_box_iff mul_mem_box_iff_of_le mul_mem_box_of_le mul_sub_one_mem_levelSet one_mem_box one_mem_boxSupport one_mem_unipotentBox parameterBase_isMulLeftInvariant point_eq_mul principalAverage principalAverageGLBorel principalAverageGLLocallyCompact principalAverageGLMeasurable principalAverageGLSecondCountable principalAverageLocalField principalAverageMatrixLocallyCompact principalAverageT2 principalAverageTopology principalAverageValuativeRel principalAverage_box_integral principalAverage_equivariant principalAverage_extraction principalAverage_mul principalAveragingMeasure principalAveragingMeasure_ae_det_norm principalAveragingMeasure_ae_mem principalAveragingMeasure_finite principalAveragingMeasure_fixed principalAveragingMeasure_integral principalAveragingMeasure_mass principalAveragingMeasure_weighted_integral principalLevel_firstRow principalLevel_le_integral principalLevel_mass_pos principalMeasure_extraction principalMeasure_weighted_extraction principalWeightedGLBorel principalWeightedGLMeasurable principalWeightedLocalField principalWeightedScalarAverage principalWeightedTopology principalWeightedValuativeRel rankOneEmbedding_eq_point rankOneModelValues_subset rankOneModel_convergesOnRight_of_matrix rankOne_support_of_principalLevel restrict_boxSupport_lt_top restrict_boxSupport_pos standardCharacter_eq_one tailMeasure_torusBox tailMeasure_torusBox_lt_top tailMeasure_torusBox_pos torusBox torusBox_eq_pi torusFactor_mem uniformBoxGLBorel uniformBoxGLMeasurable uniformBoxLocalField uniformBoxSecondCountable uniformBoxT2 uniformBoxTopology uniformBoxUnipotentBorel uniformBoxUnipotentMeasurable uniformBoxUnitsBorel uniformBoxUnitsMeasurable uniformBoxUnitsSecondCountable uniformBoxValuativeRel uniformBox_mul_principalLevel uniform_box_extraction unipotentBox unipotentBox_eq_entry_preimage unipotentBox_subset unipotentHaar_unipotentBox_lt_top unipotentHaar_unipotentBox_lt_top_all unipotentHaar_unipotentBox_pos unipotentLocallyCompact unipotentSecondCountable unipotent_mul_rankOne_apply unipotent_mul_rankOne_apply_zero unitLevel unitLevel_le_integralUnits unitLevel_measure_le unitLevel_measure_pos unitsSecondCountable weight_smul_integrand
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

universe uF

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance principalWeightedGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance principalWeightedGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

variable {n : ℕ}

/-- A right factor with determinant norm one does not change any spectral
determinant weight. -/
theorem determinantWeight_mul_of_norm_one
    (g k : Langlands.GeneralLinear (n + 1) F)
    (hk : abv (Matrix.det k.val) = 1) (s : ℂ) :
    determinantWeight abv (g * k) s = determinantWeight abv g s := by
  simp only [determinantWeight, Units.val_mul, Matrix.det_mul, map_mul, hk, mul_one]

/-- The scalar embedding preserves the actual determinant weight. -/
theorem determinantWeight_rankOneEmbedding (m : ℕ)
    (g : Langlands.GeneralLinear (0 + 1) F) (s : ℂ) :
    determinantWeight abv (rankOneEmbedding m g) s = determinantWeight abv g s := by
  have hd : Matrix.GeneralLinearGroup.det (rankOneEmbedding m g) =
      Matrix.GeneralLinearGroup.det g := by
    simp [rankOneEmbedding, det_diagonalUnits, Fin.prod_univ_succ]
  unfold determinantWeight
  exact congrArg (fun x : Fˣ => ((abv (x : F) : ℝ) : ℂ) ^ s) hd

/-- Spectral multiplication preserves the standard left character. -/
theorem determinantWeighted_equivariant
    (ψ : UnitaryAdditiveCharacter F)
    (W : Langlands.GeneralLinear (n + 1) F → ℂ)
    (heq : ∀ u : upperUnipotent (n + 1) F, ∀ h,
      W (u.val * h) = (standardCharacter ψ n u : ℂ) * W h)
    (s : ℂ) (u : upperUnipotent (n + 1) F) (g) :
    W (u.val * g) * determinantWeight abv (u.val * g) s =
      (standardCharacter ψ n u : ℂ) * (W g * determinantWeight abv g s) := by
  have hd : determinantWeight abv (u.val * g) s = determinantWeight abv g s := by
    unfold determinantWeight
    rw [Units.val_mul, det_unipotent_mul]
  rw [heq, hd, mul_assoc]

/-- The same compact principal measure factors out every spectral weight.
The identity uses its actual determinant-norm-one support. -/
theorem principalAveragingMeasure_weighted_integral (a : ℕ) (C : ℝ)
    (W : Langlands.GeneralLinear (n + 1) F → ℂ)
    (g : Langlands.GeneralLinear (n + 1) F) (s : ℂ) :
    ∫ k, W (g * k) * determinantWeight abv (g * k) s
        ∂principalAveragingMeasure F a C =
      (∫ k, W (g * k) ∂principalAveragingMeasure F a C) *
        determinantWeight abv g s := by
  calc
    _ = ∫ k, W (g * k) * determinantWeight abv g s
        ∂principalAveragingMeasure F a C := by
      apply integral_congr_ae
      filter_upwards [principalAveragingMeasure_ae_det_norm F a C] with k hk
      rw [determinantWeight_mul_of_norm_one F g k hk]
    _ = _ := integral_mul_const _ _

/-- The scalar restriction of a model function after the fixed principal
compact average, with its spectral determinant weight. -/
def principalWeightedScalarAverage {m : ℕ} (a : ℕ) (C : ℝ)
    (W : Langlands.GeneralLinear (m + 1 + 1) F → ℂ) (s : ℂ)
    (g : Langlands.GeneralLinear (0 + 1) F) : ℂ :=
  (∫ k, W (rankOneEmbedding m g * k) ∂principalAveragingMeasure F a C) *
    determinantWeight abv g s

/-- Universal original extraction at every complex spectral parameter, with
one test, one compact measure, and genuine convergence of the scalar average. -/
theorem principalMeasure_weighted_extraction (ψ : UnitaryAdditiveCharacter F)
    {m : ℕ} {a : ℕ} (ha : 0 < a)
    (hA : 0 ≤ (⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
    (W : Langlands.GeneralLinear (m + 1 + 1) F → ℂ) (hW : Continuous W)
    (heq : ∀ u : upperUnipotent (m + 1 + 1) F, ∀ h,
      W (u.val * h) = (standardCharacter ψ (m + 1) u : ℂ) * W h)
    (s : ℂ)
    (hconv : Integrable (GodementJacquet.matrixIntegrand abv
      (boxLatticeTest F ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
        ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a) s W)
      (generalLinearHaar F (m + 1))) :
    let C := boxExtractionConstant F (n := m + 1)
      ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
      ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a
    Integrable (principalWeightedScalarAverage F a C W s)
      (glOneMeasure F (m + 1)) ∧
    GodementJacquet.matrixIntegral abv (generalLinearHaar F (m + 1))
      (boxLatticeTest F ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
        ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a) s W =
      ∫ g, principalWeightedScalarAverage F a C W s g
        ∂glOneMeasure F (m + 1) := by
  dsimp only [principalWeightedScalarAverage]
  have hc : Integrable (fun h =>
      boxLatticeTest F ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
        ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a h.val *
          (W h * determinantWeight abv h s))
      (generalLinearHaar F (m + 1)) := by
    change Integrable (fun h =>
      boxLatticeTest F ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
        ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a h.val * W h *
          determinantWeight abv h s) (generalLinearHaar F (m + 1)) at hconv
    simpa only [mul_assoc] using hconv
  obtain ⟨hi, hv⟩ := principalMeasure_extraction F ψ ha hA
    (fun h => W h * determinantWeight abv h s)
    (hW.mul (continuous_determinantWeight F _ s))
    (determinantWeighted_equivariant F ψ W heq s) hc
  simp_rw [principalAveragingMeasure_weighted_integral,
    determinantWeight_rankOneEmbedding] at hi hv
  refine ⟨hi, ?_⟩
  simpa only [GodementJacquet.matrixIntegral, GodementJacquet.matrixIntegrand,
    mul_assoc] using hv

end Langlands.AllField.RankinSelberg.RankOneBox
