import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedDualTransport
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalFixedDual
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalOriginal
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylTransport
/-! # The actual leading-sign and Weyl transport of the dual Fourier integral -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NNReal

namespace Langlands.AllField.Conductor
open Langlands.Conductor
open Langlands.AllField.Conductor

open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
universe uK

end Langlands.AllField.Conductor

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement RankOneCharacterReductionStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement boxLatticeTest_fourier_rightLeadingSign boxLatticeTest_rightLeadingSign compactParametersBorel compactParametersGLBorel compactParametersGLLocallyCompact compactParametersGLMeasurable compactParametersGLSecondCountable compactParametersLocalField compactParametersMeasurable compactParametersNBorel compactParametersNMeasurable compactParametersSecondCountable compactParametersT2 compactParametersTopology compactParametersTotallyDisconnected compactParametersValuativeRel continuous_principalSignedBlockPoint determinantNorm_rankOneSignedBlockWeyl determinantNorm_rankOneSignedWeyl determinantNorm_rankOneWeylLeadingSign determinantWeight_principalSignedBlockPoint diagonalConj_map diagonal_abs_bound diagonal_abs_last exists_rankOneCutoff exists_rankOneEmbedding_support glCoefficientModel_isOfWhittakerType glOneWeight_eq_determinantWeight glOneWeight_smul_natSucc integrable_generalLinear_one_natWeight_iff integrable_generalLinear_one_prod_natWeight_iff integrable_principalModelBlockIntegrand_of_fixed integrable_principalModelFourierIntegrand_signedDual_iff integrable_prod_generalLinear_one_natWeight_iff integral_generalLinear_one_natWeight integral_generalLinear_one_prod_natWeight integral_principalModelBlockIntegrand_of_fixed integral_principalModelFourierIntegrand_signedDual integral_prod_generalLinear_one_natWeight isEqualRankLPolynomial_characterChange_normalized isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit matrixComparisonModelsTopology matrixComparisonPositiveBorel matrixComparisonPositiveDisconnected matrixComparisonPositiveGLBorel matrixComparisonPositiveGLMeasurable matrixComparisonPositiveLocalField matrixComparisonPositiveMeasurable matrixComparisonPositiveQuotientBorel matrixComparisonPositiveQuotientMeasurable matrixComparisonPositiveT2 matrixComparisonPositiveTopology matrixComparisonPositiveUnipotentBorel matrixComparisonPositiveUnipotentMeasurable matrixComparisonPositiveValuation normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow orbitBlocksBorel orbitBlocksLocalField orbitBlocksMeasurable orbitBlocksNBorel orbitBlocksNLocallyCompact orbitBlocksNMeasurable orbitBlocksNSecondCountable orbitBlocksSecondCountable orbitBlocksSigmaCompact orbitBlocksT2 orbitBlocksTopology orbitBlocksTotallyDisconnected orbitBlocksValuativeRel padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType parameter_glOneMeasure_block_density parameter_glOneMeasure_density principalCompactDualBorel principalCompactDualGLBorel principalCompactDualGLMeasurable principalCompactDualGLSecondCountable principalCompactDualIntegrand principalCompactDualIntegrand_reconstruct principalCompactDualLocalField principalCompactDualMeasurable principalCompactDualSecondCountable principalCompactDualT2 principalCompactDualTopology principalCompactDualTotallyDisconnected principalCompactDualUnitsBorel principalCompactDualUnitsMeasurable principalCompactDualUnitsSecondCountable principalCompactDualValuativeRel principalCompactDual_fourierOrbit_duality principalCompactDual_pairing principalCompactDual_pairing_weighted principalCompactFourier_reconstruct principalCompactKernel principalCompactKernel_ae principalCompactKernel_detNorm principalCompactKernel_of_mem principalFixedBlockIntegrand principalFixedDualBorel principalFixedDualGLBorel principalFixedDualGLMeasurable principalFixedDualGLSecondCountable principalFixedDualLocalField principalFixedDualMeasurable principalFixedDualSecondCountable principalFixedDualT2 principalFixedDualTopology principalFixedDualTotallyDisconnected principalFixedDualValuativeRel principalFixedModelDual_pairing principalModelBlockIntegrand principalModelBlockIntegrand_ae_of_fixed principalModelDualBorel principalModelDualGLBorel principalModelDualGLMeasurable principalModelDualGLSecondCountable principalModelDualLocalField principalModelDualMeasurable principalModelDualSecondCountable principalModelDualT2 principalModelDualTopology principalModelDualTotallyDisconnected principalModelDualValuativeRel principalModelDual_pairing principalModelFourierIntegrand principalModelFourierIntegrand_signedDual_eq principalSignedBlockPoint rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaFactor_of_blockZero_one rankOneGammaFactor_of_normalized_blockZero_one rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneSignedDualHomeomorph rankOneSignedDualHomeomorph_apply rankOneSignedDualHomeomorph_preserving rankOneWhittakerType rankOne_blockZero_exists_ne_zero scalarHaarBorel scalarHaarGLBorel scalarHaarGLLocallyCompact scalarHaarGLMeasurable scalarHaarGLSecondCountable scalarHaarLocalField scalarHaarMeasurable scalarHaarNullSingleton scalarHaarSecondCountable scalarHaarSigmaCompact scalarHaarT2 scalarHaarTopology scalarHaarValuativeRel signedBlockGLParameterIntegrand signedDualTransportGLBorel signedDualTransportGLMeasurable signedDualTransportLocalField signedDualTransportScalarMeasurable signedDualTransportTopology signedDualTransportValuation signedWeylGLParameterIntegrand signedWeylGL_blockGL_parameter_duality signedWeylOrbit_blockOrbit_fourier_duality signedWeylOrbit_blockOrbit_fourier_duality_averaged signedWeyl_affineBlock_fourier_duality singleton_modulus_real tsupport_boxLatticeTest_subset unequalRankCompactSupport unequalRankFiniteExpansion unequalRankGammaPropagation unequalRankIwasawaSupport unequalRankUnitSpan weylBlockBorelSpace weylBlockLocalField weylBlockMeasurableSpace weylBlockNBorelSpace weylBlockNLocallyCompact weylBlockNMeasurableSpace weylBlockNSecondCountable weylBlockSecondCountable weylBlockSigmaCompact weylBlockT2 weylBlockTopology weylBlockTotallyDisconnected weylBlockValuativeRel zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement isClopen_rectangularLatticeCoset isCompact_rectangularLatticeCoset mem_rectangularLatticeCoset padicLatticeGeometry padicRectangularFourierIntegral_exchange_left padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right rectangularLatticeCoset rectangularLatticeCosetTest rectangularLatticeCosetTest_apply
open Langlands.AllField.HarmonicAnalysis
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.Conductor
open Langlands.AllField.Conductor
open Langlands.RankinSelberg.RankOneBox hiding ModelBoxConditions PrincipalModelRealization PrincipalOriginalAssertions averagedModelCoefficient_eq_of_left_invariant box boxCoefficientBorelSpace boxCoefficientLocalField boxCoefficientMeasurableSpace boxCoefficientTopology boxCoefficientValuativeRel boxCoefficient_extraction_of_principalLevel boxCoefficient_mul_principalLevel boxCoefficient_point boxComparisonVolume boxConvergenceBorelSpace boxConvergenceLocalField boxConvergenceMeasurableSpace boxConvergenceSecondCountable boxConvergenceT2 boxConvergenceTopology boxConvergenceUnipotentBorel boxConvergenceUnipotentMeasurable boxConvergenceUnitsBorel boxConvergenceUnitsMeasurable boxConvergenceUnitsSecondCountable boxConvergenceValuativeRel boxEntry boxExtractionConstant boxExtractionConstant_pos boxLatticeCentre boxLatticeTest boxLatticeTest_apply boxLatticeTest_eq_compactOpenIndicator boxSupport boxVolumeBorelSpace boxVolumeLocalField boxVolumeMeasurableSpace boxVolumeTopology boxVolumeUnipotentBorel boxVolumeUnipotentMeasurable boxVolumeValuativeRel box_comparison_of_integrable box_eq_pi box_eq_rectangularLatticeCoset box_matrixIntegrand_eq_of_eq_on_box coe_unitLevel continuous_determinantWeight continuous_glModelFunction continuous_principalAverage continuous_rankOneEmbedding continuous_unipotent_entry cutoffUnipotent_mem_principalLevel determinantRankOne_point determinantWeight_mul_of_norm_one determinantWeight_rankOneEmbedding determinantWeighted_equivariant diagonalUnits_mem_principalLevel exists_box_averagedModelCoefficient_eq exists_box_constant exists_mem_principalLevel_mul_inv_upper exists_point_mul_of_mem_box exists_principalModelRealization glLocallyCompact glSecondCountable instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceUnitsCarrier instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceUnitsCarrier instSecondCountableTopologyCarrier instT2SpaceCarrier instT2SpaceCarrier_1 instT2SpaceCarrier_2 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 integer_of_mem_principalLevel integral_eq_of_support integral_param_of_eq inv_sub_one_mem_levelSet isCompact_box isCompact_boxEntry isCompact_unipotentBox isOpen_box isOpen_boxEntry isOpen_boxSupport isOpen_torusBox isOpen_unipotentBox isOpen_unitLevel levelSet_eq_additiveLattice lintegral_enorm_eq_of_support lintegral_param_of_eq matrixIntegrand_mul_principalLevel matrixIntegrand_point matrixLocallyCompact measurableSet_integralSubgroup measurePreserving_rshift mem_box_iff mem_box_unipotent_mul_iff mem_torusBox_of_mem_box mem_unitLevel_iff modelFunction_eq_determinantRankOne_of_mem_box modelFunction_eq_determinantRankOne_of_mem_box_of_le mul_mem_box mul_mem_box_iff mul_mem_box_iff_of_le mul_mem_box_of_le mul_sub_one_mem_levelSet one_mem_box one_mem_boxSupport one_mem_unipotentBox parameterBase_isMulLeftInvariant point_eq_mul principalAverage principalAverageGLBorel principalAverageGLLocallyCompact principalAverageGLMeasurable principalAverageGLSecondCountable principalAverageLocalField principalAverageMatrixLocallyCompact principalAverageT2 principalAverageTopology principalAverageValuativeRel principalAverage_box_integral principalAverage_equivariant principalAverage_extraction principalAverage_mul principalAveragingMeasure principalAveragingMeasure_ae_det_norm principalAveragingMeasure_ae_mem principalAveragingMeasure_finite principalAveragingMeasure_fixed principalAveragingMeasure_integral principalAveragingMeasure_mass principalAveragingMeasure_weighted_integral principalLevel_firstRow principalLevel_le_integral principalLevel_mass_pos principalMeasure_extraction principalMeasure_weighted_extraction principalOriginalAssertions_of_realization principalOriginalGLBorel principalOriginalGLMeasurable principalOriginalLocalField principalOriginalTopology principalOriginalValuativeRel principalOriginal_value principalRealizationGLBorel principalRealizationGLMeasurable principalRealizationLocalField principalRealizationTopology principalRealizationValuativeRel principalWeightedGLBorel principalWeightedGLMeasurable principalWeightedLocalField principalWeightedScalarAverage principalWeightedTopology principalWeightedValuativeRel rankOneEmbedding_eq_point rankOneModelValues_subset rankOneModel_convergesOnRight_of_matrix rankOne_support_of_principalLevel restrict_boxSupport_lt_top restrict_boxSupport_pos standardCharacter_eq_one tailMeasure_torusBox tailMeasure_torusBox_lt_top tailMeasure_torusBox_pos torusBox torusBox_eq_pi torusFactor_mem uniformBoxGLBorel uniformBoxGLMeasurable uniformBoxLocalField uniformBoxSecondCountable uniformBoxT2 uniformBoxTopology uniformBoxUnipotentBorel uniformBoxUnipotentMeasurable uniformBoxUnitsBorel uniformBoxUnitsMeasurable uniformBoxUnitsSecondCountable uniformBoxValuativeRel uniformBox_mul_principalLevel uniform_box_extraction unipotentBox unipotentBox_eq_entry_preimage unipotentBox_subset unipotentHaar_unipotentBox_lt_top unipotentHaar_unipotentBox_lt_top_all unipotentHaar_unipotentBox_pos unipotentLocallyCompact unipotentSecondCountable unipotent_mul_rankOne_apply unipotent_mul_rankOne_apply_zero unitLevel unitLevel_le_integralUnits unitLevel_measure_le unitLevel_measure_pos unitsSecondCountable weight_smul_integrand
open Langlands.AllField.RankinSelberg.RankOneBox
universe uF
variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance signedDualTransportScalarMeasurable : MeasurableSpace F := borel _
local instance signedDualTransportGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance signedDualTransportGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
local notation "𝓛" => (Langlands.LocalFieldData.additiveLattice (⟨⟩ : LocalFieldData F))

/-- The full original box test is invariant under its leading-column sign. -/
theorem boxLatticeTest_rightLeadingSign (n : ℕ) (A q : ℤ) (a : ℕ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) F) :
    boxLatticeTest F A q a (M * (rankOneWeylLeadingSign n).val) =
      boxLatticeTest F A q a M := by
  have hf : ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) F,
      X ∈ box F A q a → X * (rankOneWeylLeadingSign n).val ∈ box F A q a := by
    intro X hX
    rw [mem_box_iff] at hX ⊢
    simp only [rankOneWeylLeadingSign_val, Matrix.mul_diagonal]
    refine ⟨?_, ?_, ?_⟩
    · simpa only [ite_true, mul_neg_one] using (𝓛 A).neg_mem hX.1
    · intro j hj
      simpa only [ite_eq_right hj, mul_one] using hX.2.1 j hj
    · intro i hi j
      by_cases hj : j = 0
      · subst j
        have hz : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i 0 = 0 := by
          simp [hi]
        simp only [ite_true, mul_neg_one, hz, sub_zero]
        rw [levelSet_eq_additiveLattice] at hX ⊢
        exact (𝓛 (-(a : ℤ))).neg_mem (by simpa only [hz, sub_zero, SetLike.mem_coe] using hX.2.2 i hi 0)
      · simpa only [ite_eq_right hj, mul_one] using hX.2.2 i hi j
  have he : M * (rankOneWeylLeadingSign n).val ∈ box F A q a ↔ M ∈ box F A q a := by
    refine ⟨fun h => ?_, hf M⟩
    have h' := hf _ h
    simpa only [Matrix.mul_assoc, ← Units.val_mul, rankOneWeylLeadingSign_mul_self,
      Units.val_one, Matrix.mul_one] using h'
  simp only [boxLatticeTest_apply]
  by_cases hM : M ∈ box F A q a
  · rw [Set.indicator_of_mem (he.mpr hM), Set.indicator_of_mem hM]
  · rw [Set.indicator_of_notMem (fun h => hM (he.mp h)), Set.indicator_of_notMem hM]

theorem determinantNorm_rankOneWeylLeadingSign (n : ℕ) :
    (⟨⟩ : LocalFieldData F).determinantNorm (n + 1) (rankOneWeylLeadingSign n) = 1 := by
  apply (⟨⟩ : LocalFieldData F).determinantNorm_eq_one_of_pow_eq_one _
    (by decide : 2 ≠ 0)
  rw [pow_two, rankOneWeylLeadingSign_mul_self]

theorem determinantNorm_rankOneSignedWeyl (n : ℕ) :
    (⟨⟩ : LocalFieldData F).determinantNorm (n + 1) (rankOneSignedWeyl n) = 1 := by
  have hA : (⟨⟩ : LocalFieldData F).determinantNorm (n + 1) (rankOneWeylAlternating n) = 1 := by
    apply (⟨⟩ : LocalFieldData F).determinantNorm_eq_one_of_pow_eq_one _
      (by decide : 2 ≠ 0)
    rw [pow_two, rankOneWeylAlternating_mul_self]
  simp only [rankOneSignedWeyl, map_mul, hA,
    (⟨⟩ : LocalFieldData F).determinantNorm_weylLong, one_mul]

/-- Every actual Fourier partner retains this exact leading-column symmetry. -/
theorem boxLatticeTest_fourier_rightLeadingSign
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (n : ℕ) (A q : ℤ) (a : ℕ) (ΦHat : GodementJacquet.MatrixTestFunction n F)
    (hp : Langlands.AllField.GodementJacquet.Padic.MatrixFourierPair F ψ ν (boxLatticeTest F A q a) ΦHat)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) F) :
    ΦHat (M * (rankOneWeylLeadingSign n).val) = ΦHat M := by
  have h := Langlands.AllField.GodementJacquet.padicMatrixFourierPair_leftRight_invariant F
    (⟨⟩ : LocalFieldData F) n ψ ν 1 (rankOneWeylLeadingSign n) (map_one _)
    (determinantNorm_rankOneWeylLeadingSign F n) _ ΦHat hp
    (by intro Y; simpa using boxLatticeTest_rightLeadingSign F n A q a Y) M
  simpa only [map_one, Units.val_one, Matrix.one_mul,
    inverseTranspose_rankOneWeylLeadingSign] using h

/-- The actual two-sided group substitution used in the signed Fourier passage. -/
def rankOneSignedDualHomeomorph (n : ℕ) :
    Langlands.GeneralLinear (n + 1) F ≃ₜ Langlands.GeneralLinear (n + 1) F :=
  (Homeomorph.mulLeft (rankOneSignedWeyl n)).trans
    (Homeomorph.mulRight (rankOneWeylLeadingSign n))

@[simp] theorem rankOneSignedDualHomeomorph_apply (n : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    rankOneSignedDualHomeomorph F n g = rankOneSignedWeyl n * g * rankOneWeylLeadingSign n := rfl

/-- Left and right Haar invariance give exact measure preservation. -/
theorem rankOneSignedDualHomeomorph_preserving (n : ℕ) :
    MeasurePreserving (rankOneSignedDualHomeomorph F n)
      (generalLinearHaar F n) (generalLinearHaar F n) :=
  (measurePreserving_mul_right (generalLinearHaar F n) (rankOneWeylLeadingSign n)).comp
    (measurePreserving_mul_left (generalLinearHaar F n) (rankOneSignedWeyl n))

/-- The complete integrands agree under the actual measure-preserving substitution. -/
theorem principalModelFourierIntegrand_signedDual_eq
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (m a : ℕ) (s : ℂ) (W : Langlands.GeneralLinear (m + 2) F → ℂ)
    (ΦHat : GodementJacquet.MatrixTestFunction (m + 1) F)
    (hp : Langlands.AllField.GodementJacquet.Padic.MatrixFourierPair F ψ ν
      (boxLatticeTest F ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
        ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a) ΦHat)
    (h : Langlands.GeneralLinear (m + 2) F) :
    principalModelFourierIntegrand F ψ ν m a s (rankOneSignedDualFunction (m + 1) W) h =
      GodementJacquet.matrixIntegrand abv ΦHat s (GodementJacquet.coefficientIota W)
        (rankOneSignedDualHomeomorph F (m + 1) h) := by
  have hE : abv (rankOneWeylLeadingSign (m + 1)).val.det = 1 :=
    congrArg (fun x : ℝ≥0ˣ => ((x : ℝ≥0) : ℝ))
      (determinantNorm_rankOneWeylLeadingSign F (m + 1))
  have hw : abv (rankOneSignedWeyl (m + 1)).val.det = 1 :=
    congrArg (fun x : ℝ≥0ˣ => ((x : ℝ≥0) : ℝ))
      (determinantNorm_rankOneSignedWeyl F (m + 1))
  have hweightE : determinantWeight abv (rankOneWeylLeadingSign (m + 1)) s = 1 := by
    simp only [determinantWeight, hE, Complex.ofReal_one, Complex.one_cpow]
  have hweightw : determinantWeight abv (rankOneSignedWeyl (m + 1)) s = 1 := by
    simp only [determinantWeight, hw, Complex.ofReal_one, Complex.one_cpow]
  simp only [principalModelFourierIntegrand, rankOneSignedDualHomeomorph_apply,
    GodementJacquet.matrixIntegrand, rankOneSignedDualFunction_eq_iota,
    determinantWeight_mul, hweightE, hweightw, one_mul, mul_one, Units.val_mul,
    boxLatticeTest_fourier_rightLeadingSign F ψ ν _ _ _ _ ΦHat hp,
    ← (hp _).2]
  ring

/-- Genuine raw inverse-transpose convergence is equivalent to convergence of
its signed same-character Fourier restriction. -/
theorem integrable_principalModelFourierIntegrand_signedDual_iff
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (m a : ℕ) (s : ℂ) (W : Langlands.GeneralLinear (m + 2) F → ℂ)
    (ΦHat : GodementJacquet.MatrixTestFunction (m + 1) F)
    (hp : Langlands.AllField.GodementJacquet.Padic.MatrixFourierPair F ψ ν
      (boxLatticeTest F ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
        ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a) ΦHat) :
    Integrable (principalModelFourierIntegrand F ψ ν m a s (rankOneSignedDualFunction (m + 1) W))
      (generalLinearHaar F (m + 1)) ↔
    Integrable (GodementJacquet.matrixIntegrand abv ΦHat s (GodementJacquet.coefficientIota W))
      (generalLinearHaar F (m + 1)) := by
  have he : principalModelFourierIntegrand F ψ ν m a s (rankOneSignedDualFunction (m + 1) W) =
      (GodementJacquet.matrixIntegrand abv ΦHat s (GodementJacquet.coefficientIota W)) ∘
        rankOneSignedDualHomeomorph F (m + 1) :=
    funext (principalModelFourierIntegrand_signedDual_eq F ψ ν m a s W ΦHat hp)
  rw [he]
  exact (rankOneSignedDualHomeomorph_preserving F (m + 1)).integrable_comp_emb
    (rankOneSignedDualHomeomorph F (m + 1)).measurableEmbedding

/-- This substitution contributes no scalar to the actual dual matrix value. -/
theorem integral_principalModelFourierIntegrand_signedDual
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (m a : ℕ) (s : ℂ) (W : Langlands.GeneralLinear (m + 2) F → ℂ)
    (ΦHat : GodementJacquet.MatrixTestFunction (m + 1) F)
    (hp : Langlands.AllField.GodementJacquet.Padic.MatrixFourierPair F ψ ν
      (boxLatticeTest F ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
        ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a) ΦHat) :
    (∫ h, principalModelFourierIntegrand F ψ ν m a s (rankOneSignedDualFunction (m + 1) W) h
      ∂generalLinearHaar F (m + 1)) =
    GodementJacquet.matrixIntegral abv (generalLinearHaar F (m + 1)) ΦHat s
      (GodementJacquet.coefficientIota W) := by
  simp_rw [principalModelFourierIntegrand_signedDual_eq F ψ ν m a s W ΦHat hp]
  exact (rankOneSignedDualHomeomorph_preserving F (m + 1)).integral_comp
    (rankOneSignedDualHomeomorph F (m + 1)).measurableEmbedding _

end Langlands.AllField.RankinSelberg
