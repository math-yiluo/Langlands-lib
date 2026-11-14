import Langlands.Representation.GodementJacquet.SupercuspidalFourierRegularEquation
import Langlands.AllField.Representation.GodementJacquet.RegularMatrixConvolutionExchange
import Langlands.AllField.Representation.GodementJacquet.SupercuspidalMonomialComparison
/-! # The supercuspidal equation on Fourier-regular matrix tests -/

noncomputable section

namespace Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData aestronglyMeasurable_dualParabolicIntegrand compactMatrixLaurentBorelSpace compactMatrixLaurentLocalField compactMatrixLaurentMeasurableSpace compactMatrixLaurentTopology compactMatrixLaurentValuativeRel comparisonBorel comparisonDisconnected comparisonLocalField comparisonMeasurable comparisonT2 comparisonTopology comparisonValuativeRel convolutionExchangeBorel convolutionExchangeDisconnected convolutionExchangeGLBorel convolutionExchangeGLMeasurable convolutionExchangeLocalField convolutionExchangeMeasurable convolutionExchangeT2 convolutionExchangeTopology convolutionExchangeValuation determinantWeight_inv_inverseTranspose determinantWeight_locallyConstant determinantWeight_neg_dimension determinantWeight_shift_spectral determinantWeight_sub_spectral dualParabolicBorelSpace dualParabolicGLBorelSpace dualParabolicGLMeasurableSpace dualParabolicIntegrand dualParabolicLocalField dualParabolicMatrixSecondCountable dualParabolicMeasurableSpace dualParabolicSecondCountable dualParabolicT2Space dualParabolicTopology dualParabolicTotallyDisconnected dualParabolicValuativeRel dualWeightedRegularMatrixTest dualWeightedRegularMatrixTest_apply dualWeightedRegularMatrixTest_convolution_cross dualWeightedRegularMatrixTest_convolution_left dualWeightedRegularMatrixTest_convolution_right exists_fourierRegular_constant_output exists_fourierRegular_constant_output_of_pairing exists_integral_regularMatrix_density exists_laurent_integral_of_hasCompactSupport exists_laurent_matrixIntegral_of_hasCompactSupport exists_laurent_regularMatrixZetaOperator_dual_sub exists_laurent_scalar_of_fourierRegular_cross exists_monomial_fourierRegular_inverseTranspose exists_monomial_scalar_of_fourierRegular_cross exists_scalar_of_fourierRegularMatrixZetaOperator_cross exists_smoothFunctional_ne_zero fourierRegularEquationBorel fourierRegularEquationDisconnected fourierRegularEquationLocalField fourierRegularEquationMeasurable fourierRegularEquationT2 fourierRegularEquationTopology fourierRegularEquationValuation fourierRegularInverseTransposeZetaOperator fourierRegularInverseTransposeZetaOperator_apply fourierRegularMatrixTranslate fourierRegularMatrixTranslate_apply fourierRegularMatrixZetaOperator fourierRegularMatrixZetaOperator_apply fourierRegularMatrixZetaOperator_output_surjective fourierRegularMatrixZetaOperator_separates fourierRegularMonomialOutputs generalLinearHaar_measurePreserving_inverseTranspose instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 integrable_comp_lowerLeft integrable_integral_dualParabolicIntegrand integrable_integral_dualParabolic_levi integral_comp_lowerLeft intertwining_of_commutes_fourierRegularMatrixZetaOperator iotaMatrixRationalValues jpssI2 jpssI3 laurentComparisonBorel laurentComparisonDisconnected laurentComparisonGLBorel laurentComparisonGLMeasurable laurentComparisonLocalField laurentComparisonMeasurable laurentComparisonT2 laurentComparisonTopology laurentComparisonValuativeRel leftRightTranslate_mem_fourierRegularMatrixTests map_mulLeftMeasurableEquiv matrixIntegral matrixIntegral_eq_of_fourierRegular_inverseTranspose matrixIntegrand matrixRationalValues measurable_inverseTranspose_val monomialBorel monomialComparisonBorel monomialComparisonDisconnected monomialComparisonLocalField monomialComparisonMeasurable monomialComparisonT2 monomialComparisonTopology monomialComparisonValuativeRel monomialDisconnected monomialGLBorel monomialGLMeasurable monomialLocalField monomialMeasurable monomialT2 monomialTopology monomialValuativeRel mulLeftMeasurableEquiv mulLeftMeasurableEquiv_apply nonzeroZetaLocalField nonzeroZetaTopology nonzeroZetaValuativeRel rectangularFourierEquiv_inverseTranspose_translate rectangularFourierEquiv_inverseTranspose_translate_of_mem regularDensityBorel regularDensityGLBorel regularDensityGLMeasurable regularDensityLocalField regularDensityMeasurable regularDensitySecondCountable regularDensityT2 regularDensityTopology regularDensityValuation regularMatrixZetaGLBorel regularMatrixZetaGLMeasurable regularMatrixZetaLocalField regularMatrixZetaOperator regularMatrixZetaOperator_dual regularMatrixZetaOperator_eq_of_detNorm_support regularMatrixZetaOperator_inverseTranspose regularMatrixZetaOperator_inverseTranspose_cross regularMatrixZetaOperator_leftTranslate regularMatrixZetaTopology regularMatrixZetaValuation representation_mem_fourierRegularMonomialOutputs scalar_ne_zero_of_fourierRegular_comparison span_fourierRegularMonomialOutputs_eq_top translatesBorel translatesDisconnected translatesLocalField translatesMeasurable translatesT2 translatesTopology translatesValuativeRel weightedRegularMatrixTest weightedRegularMatrixTest_apply weightedRegularMatrixTest_leftTranslate whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData determinantNorm_eq_one_of_mem_conjugateUnipotent determinantUnitTestToMatrixTest determinantUnitTestToMatrixTest_apply determinantUnitTestToMatrixTest_eq_zero hasCompactSupport_determinantUnit_coefficient iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues oneBlockDeterminantUnitHomeomorph supercuspidalCutoffFourierEvaluation supercuspidalCutoffMatrixTest supercuspidalCutoffMatrixTest_apply supercuspidalCutoffMatrixTest_apply_of_not_mem supercuspidalCutoffMatrixTest_fourier_eq_zero_of_stabilizer supercuspidalCutoffMatrixTest_fourier_right supercuspidalCutoffMatrixTest_fourier_singular supercuspidalCutoffMatrixTest_mem_fourierRegularMatrixTests supercuspidalCutoffMatrixTest_right supercuspidalCutoffMatrixTest_singular supercuspidalDeterminantUnitCoefficient whittakerRationalValues
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement PadicSelfDualMeasureExistsStatement measurePreserving_rectangular_mul_mul padicLatticeGeometry padicRectangularFourierIntegral_exchange_left padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicScalarHaarScaling padicSelfDualMeasureExists padicSquareFourierIntegral_crossExchange padicSquareFourierIntegral_transposeRight rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankTrilinearUniquenessStatement IsPadicPairGammaFactor LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map disjoint_determinantSlice equalRankContinuedForms equalRankFrobenius equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def exists_rankOneCutoff exists_rankOneEmbedding_support iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice rankOneModelValues_subset_whittakerRationalValues rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance fourierRegularEquationT2 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance fourierRegularEquationDisconnected : TotallyDisconnectedSpace F :=
  (padicLatticeGeometry F (⟨⟩ : LocalFieldData F)).1
local instance fourierRegularEquationMeasurable : MeasurableSpace F := borel _
local instance fourierRegularEquationBorel : BorelSpace F := ⟨rfl⟩

variable {m : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The actual inverse-transpose zeta operator at the complementary exponent,
after the actual plus Fourier transform on the Fourier-regular subspace. -/
def fourierRegularInverseTransposeZetaOperator
    (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
    (hι : IsSmooth (ρ.comp
      (GeneralLinear.inverseTranspose (m + 1) F).toMonoidHom))
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (s : ℂ) :
    fourierRegularMatrixTests (m + 1) ψ ν hsd →ₗ[ℂ] Module.End ℂ V :=
  (fourierRegularMatrixZetaOperator F
    (ρ.comp (GeneralLinear.inverseTranspose (m + 1) F).toMonoidHom)
      hι ψ ν hsd ((m + 1 : ℕ) - s)).comp
    (fourierRegularMatrixFourierEquiv (m + 1) ψ ν hsd).toLinearMap

@[simp] theorem fourierRegularInverseTransposeZetaOperator_apply
    (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
    (hι : IsSmooth (ρ.comp
      (GeneralLinear.inverseTranspose (m + 1) F).toMonoidHom))
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (s : ℂ)
    (Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd) :
    fourierRegularInverseTransposeZetaOperator F ρ hι ψ ν hsd s Φ =
      regularMatrixZetaOperator F
        (ρ.comp (GeneralLinear.inverseTranspose (m + 1) F).toMonoidHom)
        hι ((m + 1 : ℕ) - s)
        ⟨rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Φ.val, Φ.property.2⟩ := rfl

/-- On Fourier-regular tests, the actual supercuspidal functional equation has
one nonzero monomial for all spectral parameters, with no cross premise. -/
theorem exists_monomial_fourierRegular_inverseTranspose
    (hm : 0 < m)
    (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (hi : ρ.IsIrreducible)
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) :
    ∃ (c : ℂˣ) (k : ℤ), ∀ (s : ℂ)
      (Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd),
      fourierRegularInverseTransposeZetaOperator F ρ
          (GeneralLinear.isSupercuspidal_comp_inverseTranspose ρ hρ).1.1 ψ ν hsd s Φ =
        ((c : ℂ) * spectralPoint (⟨⟩ : LocalFieldData F).residueCardinality s ^ k) •
          fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ := by
  have hι := GeneralLinear.isSupercuspidal_comp_inverseTranspose ρ hρ
  obtain ⟨c, k, hck⟩ := exists_monomial_scalar_of_fourierRegular_cross F hm ρ hρ hi
    (ρ.comp (GeneralLinear.inverseTranspose (m + 1) F).toMonoidHom) hι
    ψ ν hsd ((m + 1 : ℕ) : ℂ) (fun s Φ Ψ => by
      exact (regularMatrixZetaOperator_inverseTranspose_cross F ρ hρ.1.1 hι.1.1
        ψ ν hsd s Φ Ψ).symm)
  exact ⟨c, k, hck⟩

/-- Evaluation of the operator equation gives the literal matrix-integral
equation for every vector and algebraic functional. -/
theorem matrixIntegral_eq_of_fourierRegular_inverseTranspose
    (ρ : Representation ℂ (GeneralLinear (m + 1) F) V)
    (hρ : IsSmooth ρ)
    (hι : IsSmooth (ρ.comp
      (GeneralLinear.inverseTranspose (m + 1) F).toMonoidHom))
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (s a : ℂ)
    (Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd)
    (hFE : fourierRegularInverseTransposeZetaOperator F ρ hι ψ ν hsd s Φ =
      a • fourierRegularMatrixZetaOperator F ρ hρ ψ ν hsd s Φ)
    (v : V) (ℓ : Module.Dual ℂ V) :
    matrixIntegral F (rectangularFourierEquiv ψ ν (m + 1) (m + 1) hsd Φ.val)
        ((m + 1 : ℕ) - s)
        (fun g => ℓ (ρ (GeneralLinear.inverseTranspose (m + 1) F g) v)) =
      a * matrixIntegral F Φ.val s (fun g => ℓ (ρ g v)) := by
  have he := congrArg (fun L : Module.End ℂ V => ℓ (L v)) hFE
  simpa only [fourierRegularInverseTransposeZetaOperator_apply,
    fourierRegularMatrixZetaOperator_apply, LinearMap.smul_apply,
    map_smul, smul_eq_mul, regularMatrixZetaOperator_dual,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using he

end Langlands.AllField.GodementJacquet.Padic
