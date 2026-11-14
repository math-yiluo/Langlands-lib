import Langlands.Representation.GodementJacquet.SupercuspidalMatrixRationalExtension
import Langlands.AllField.Representation.GodementJacquet.FourierRegularRationalEquation
import Langlands.AllField.Representation.GodementJacquet.SupercuspidalMatrixPairingExtension
/-! # The rational supercuspidal equation for arbitrary matrix tests -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData aestronglyMeasurable_dualParabolicIntegrand compactMatrixLaurentBorelSpace compactMatrixLaurentLocalField compactMatrixLaurentMeasurableSpace compactMatrixLaurentTopology compactMatrixLaurentValuativeRel compactMatrixSmoothing_pairing comparisonBorel comparisonDisconnected comparisonLocalField comparisonMeasurable comparisonT2 comparisonTopology comparisonValuativeRel conjugateSupercuspidalCutoffGroupTest conjugateSupercuspidalCutoffGroupTest_apply conjugateSupercuspidalCutoffGroupTest_conjugate conjugateSupercuspidalCutoffGroupTest_eq_zero continuedMatrixCovarianceBorel continuedMatrixCovarianceDisconnected continuedMatrixCovarianceGLBorel continuedMatrixCovarianceGLMeasurable continuedMatrixCovarianceLocalField continuedMatrixCovarianceMeasurable continuedMatrixCovarianceT2 continuedMatrixCovarianceTopology continuedMatrixCovarianceValuation convolutionExchangeBorel convolutionExchangeDisconnected convolutionExchangeGLBorel convolutionExchangeGLMeasurable convolutionExchangeLocalField convolutionExchangeMeasurable convolutionExchangeT2 convolutionExchangeTopology convolutionExchangeValuation determinantWeight_inv_inverseTranspose determinantWeight_locallyConstant determinantWeight_neg_dimension determinantWeight_shift_spectral determinantWeight_sub_spectral dualParabolicBorelSpace dualParabolicGLBorelSpace dualParabolicGLMeasurableSpace dualParabolicIntegrand dualParabolicLocalField dualParabolicMatrixSecondCountable dualParabolicMeasurableSpace dualParabolicSecondCountable dualParabolicT2Space dualParabolicTopology dualParabolicTotallyDisconnected dualParabolicValuativeRel dualWeightedRegularMatrixTest dualWeightedRegularMatrixTest_apply dualWeightedRegularMatrixTest_convolution_cross dualWeightedRegularMatrixTest_convolution_left dualWeightedRegularMatrixTest_convolution_right epsilonMonomial_shiftedMatrixMonomialUnit exists_fourierRegular_constant_output exists_fourierRegular_constant_output_of_pairing exists_integral_regularMatrix_density exists_laurent_integral_of_hasCompactSupport exists_laurent_matrixIntegral_of_hasCompactSupport exists_laurent_regularMatrixZetaOperator_dual_sub exists_laurent_scalar_of_fourierRegular_cross exists_monomial_fourierRegular_inverseTranspose exists_monomial_scalar_of_fourierRegular_cross exists_scalar_of_fourierRegularMatrixZetaOperator_cross exists_smoothFunctional_ne_zero extensionBorel extensionDisconnected extensionGLBorel extensionGLMeasurable extensionLocalField extensionMeasurable extensionT2 extensionTopology extensionValuativeRel fourierRegularEquationBorel fourierRegularEquationDisconnected fourierRegularEquationLocalField fourierRegularEquationMeasurable fourierRegularEquationT2 fourierRegularEquationTopology fourierRegularEquationValuation fourierRegularInverseTransposeZetaOperator fourierRegularInverseTransposeZetaOperator_apply fourierRegularMatrixPairingRestriction fourierRegularMatrixPairingRestriction_apply fourierRegularMatrixTranslate fourierRegularMatrixTranslate_apply fourierRegularMatrixZetaOperator fourierRegularMatrixZetaOperator_apply fourierRegularMatrixZetaOperator_output_surjective fourierRegularMatrixZetaOperator_separates fourierRegularMonomialOutputs fourierRegularRationalBorel fourierRegularRationalDisconnected fourierRegularRationalGLBorel fourierRegularRationalGLMeasurable fourierRegularRationalLocalField fourierRegularRationalMeasurable fourierRegularRationalT2 fourierRegularRationalTopology fourierRegularRationalValuation generalLinearHaar_measurePreserving_inverseTranspose instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 integrable_comp_lowerLeft integrable_integral_dualParabolicIntegrand integrable_integral_dualParabolic_levi integral_comp_lowerLeft integratedConjugateSupercuspidalCutoff_conjugate integratedConjugateSupercuspidalCutoff_ne_zero intertwining_of_commutes_fourierRegularMatrixZetaOperator iotaFourierMatrixCoefficientRationalPairing iotaFourierMatrixCoefficientRationalPairing_spec iotaFourierMatrixCoefficientRationalPairing_translate iotaMatrixRationalValues jpssI2 jpssI3 laurentComparisonBorel laurentComparisonDisconnected laurentComparisonGLBorel laurentComparisonGLMeasurable laurentComparisonLocalField laurentComparisonMeasurable laurentComparisonT2 laurentComparisonTopology laurentComparisonValuativeRel leftRightTranslate_mem_fourierRegularMatrixTests map_mulLeftMeasurableEquiv matrixCoefficientRationalPairing matrixCoefficientRationalPairing_spec matrixCoefficientRationalPairing_translate matrixFourierEquiv_translate_of_norm_one matrixIntegral matrixIntegral_eq_of_fourierRegular_inverseTranspose matrixIntegrand matrixPairing_eq_of_fourierRegular matrixPairing_eq_zero_of_fourierRegular matrixRationalPairing_identity_of_fourierRegular_operator matrixRationalPairing_identity_of_supercuspidal_fourierRegular_operator matrixRationalValues measurable_inverseTranspose_val monomialBorel monomialComparisonBorel monomialComparisonDisconnected monomialComparisonLocalField monomialComparisonMeasurable monomialComparisonT2 monomialComparisonTopology monomialComparisonValuativeRel monomialDisconnected monomialGLBorel monomialGLMeasurable monomialLocalField monomialMeasurable monomialT2 monomialTopology monomialValuativeRel mulLeftMeasurableEquiv mulLeftMeasurableEquiv_apply nonzeroZetaLocalField nonzeroZetaTopology nonzeroZetaValuativeRel normalizedFunctionalEquation_of_fourierRegular_operator normalizedFunctionalEquation_of_supercuspidal_fourierRegular_operator outputSpanGLBorel outputSpanGLMeasurable outputSpanLocalField outputSpanTopology outputSpanValuativeRel rationalExtensionBorel rationalExtensionDisconnected rationalExtensionGLBorel rationalExtensionGLMeasurable rationalExtensionLocalField rationalExtensionMeasurable rationalExtensionT2 rationalExtensionTopology rationalExtensionValuativeRel rectangularFourierEquiv_inverseTranspose_translate rectangularFourierEquiv_inverseTranspose_translate_of_mem reflectedIotaFourierMatrixCoefficientRationalPairing reflectedIotaFourierMatrixCoefficientRationalPairing_apply reflectedIotaFourierMatrixCoefficientRationalPairing_translate regularDensityBorel regularDensityGLBorel regularDensityGLMeasurable regularDensityLocalField regularDensityMeasurable regularDensitySecondCountable regularDensityT2 regularDensityTopology regularDensityValuation regularMatrixRationalValue_eval regularMatrixZetaGLBorel regularMatrixZetaGLMeasurable regularMatrixZetaLocalField regularMatrixZetaOperator regularMatrixZetaOperator_dual regularMatrixZetaOperator_eq_of_detNorm_support regularMatrixZetaOperator_inverseTranspose regularMatrixZetaOperator_inverseTranspose_cross regularMatrixZetaOperator_leftTranslate regularMatrixZetaTopology regularMatrixZetaValuation representation_mem_fourierRegularMonomialOutputs scalar_ne_zero_of_fourierRegular_comparison shiftedMatrixMonomialUnit smoothingBorel smoothingDisconnected smoothingGLBorel smoothingGLMeasurable smoothingLocalField smoothingMeasurable smoothingT2 smoothingTopology smoothingValuativeRel span_fourierRegularMonomialOutputs_eq_top supercuspidalConjugateMatrixSmoothing supercuspidalConjugateMatrixSmoothing_eq_integratedAction supercuspidalConjugateMatrixSmoothing_mem_fourierRegularMatrixTests supercuspidalConjugateMatrixSmoothing_pairing supercuspidalCutoffGroupTest supercuspidalCutoffGroupTest_apply supercuspidalCutoffOutputSpan supercuspidalCutoffOutputSpan_apply_mem supercuspidalCutoffOutputSpan_eq_top supercuspidalMatrixSmoothing supercuspidalMatrixSmoothing_apply supercuspidalMatrixSmoothing_fourier_right supercuspidalMatrixSmoothing_fourier_singular supercuspidalMatrixSmoothing_mem_fourierRegularMatrixTests supercuspidalMatrixSmoothing_right supercuspidalMatrixSmoothing_singular transferBorel transferDisconnected transferGLBorel transferGLMeasurable transferLocalField transferMeasurable transferT2 transferTopology transferValuativeRel translatesBorel translatesDisconnected translatesLocalField translatesMeasurable translatesT2 translatesTopology translatesValuativeRel weightedRegularMatrixTest weightedRegularMatrixTest_apply weightedRegularMatrixTest_leftTranslate whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData determinantNorm_eq_one_of_mem_conjugateUnipotent determinantUnitTestToMatrixTest determinantUnitTestToMatrixTest_apply determinantUnitTestToMatrixTest_eq_zero hasCompactSupport_determinantUnit_coefficient iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues oneBlockDeterminantUnitHomeomorph supercuspidalCutoffFourierEvaluation supercuspidalCutoffMatrixTest supercuspidalCutoffMatrixTest_apply supercuspidalCutoffMatrixTest_apply_of_not_mem supercuspidalCutoffMatrixTest_fourier_eq_zero_of_stabilizer supercuspidalCutoffMatrixTest_fourier_right supercuspidalCutoffMatrixTest_fourier_singular supercuspidalCutoffMatrixTest_mem_fourierRegularMatrixTests supercuspidalCutoffMatrixTest_right supercuspidalCutoffMatrixTest_singular supercuspidalDeterminantUnitCoefficient whittakerRationalValues
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement PadicSelfDualMeasureExistsStatement measurePreserving_rectangular_mul_mul padicLatticeGeometry padicRectangularFourierIntegral_exchange_left padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicScalarHaarScaling padicSelfDualMeasureExists padicSquareFourierIntegral_crossExchange padicSquareFourierIntegral_transposeRight rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankTrilinearUniquenessStatement IsPadicPairGammaFactor LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map disjoint_determinantSlice equalRankContinuedForms equalRankFrobenius equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def exists_rankOneCutoff exists_rankOneEmbedding_support iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice rankOneModelValues_subset_whittakerRationalValues rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg
open Langlands.LocalFactor
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance rationalExtensionT2 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance rationalExtensionDisconnected : TotallyDisconnectedSpace F :=
  (padicLatticeGeometry F (⟨⟩ : LocalFieldData F)).1
local instance rationalExtensionMeasurable : MeasurableSpace F := borel _
local instance rationalExtensionBorel : BorelSpace F := ⟨rfl⟩
local instance rationalExtensionGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance rationalExtensionGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))
local notation "abvF" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
local notation "μF" => generalLinearHaar F n

/-- The actual chosen Fourier and inverse-transpose rational pairing after
the normalized spectral reflection `X ↦ q⁻¹/X`. -/
def reflectedIotaFourierMatrixCoefficientRationalPairing
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν)
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ
        (coefficientIota (matrixCoefficient ρ ℓ v)) R) :
    MatrixTestFunction n F →ₗ[ℂ] V →ₗ[ℂ] RationalFunctions :=
  (iotaFourierMatrixCoefficientRationalPairing F ψ ν hsd ρ ℓ hRat).compr₂
    (RationalReflection.subst
      (spectralReflectionUnit (Nat.zero_lt_one.trans
        (⟨⟩ : LocalFieldData F).residueCardinality_gt_one))).toLinearMap

@[simp]
theorem reflectedIotaFourierMatrixCoefficientRationalPairing_apply
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν)
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ
        (coefficientIota (matrixCoefficient ρ ℓ v)) R)
    (Φ : MatrixTestFunction n F) (v : V) :
    reflectedIotaFourierMatrixCoefficientRationalPairing F ψ ν hsd ρ ℓ hRat Φ v =
      RationalReflection.subst
        (spectralReflectionUnit (Nat.zero_lt_one.trans
          (⟨⟩ : LocalFieldData F).residueCardinality_gt_one))
        (iotaFourierMatrixCoefficientRationalPairing F ψ ν hsd ρ ℓ hRat Φ v) := rfl

/-- Rational spectral reflection preserves the norm-one translation rule. -/
theorem reflectedIotaFourierMatrixCoefficientRationalPairing_translate
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν)
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ
        (coefficientIota (matrixCoefficient ρ ℓ v)) R)
    (g : GeneralLinear (n + 1) F)
    (hg : (⟨⟩ : LocalFieldData F).determinantNorm (n + 1) g = 1)
    (Φ : MatrixTestFunction n F) (v : V) :
    reflectedIotaFourierMatrixCoefficientRationalPairing F ψ ν hsd ρ ℓ hRat
        (rectangularTranslate g Φ) v =
      reflectedIotaFourierMatrixCoefficientRationalPairing F ψ ν hsd ρ ℓ hRat
        Φ (ρ g⁻¹ v) := by
  simp only [reflectedIotaFourierMatrixCoefficientRationalPairing_apply,
    iotaFourierMatrixCoefficientRationalPairing_translate F ψ ν hsd ρ ℓ hRat g hg]

/-- The global Fourier-regular operator equation extends to the actual
reflected rational pairings for every full-matrix test. -/
theorem matrixRationalPairing_identity_of_supercuspidal_fourierRegular_operator
    (hn : 0 < n)
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
    (hρ : IsSupercuspidal ρ) (hi : ρ.IsIrreducible)
    (hι : IsSupercuspidal (ρ.comp (inverseTranspose (n + 1) F).toMonoidHom))
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (c : ℂˣ) (k : ℤ)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ (matrixCoefficient ρ ℓ v) R)
    (hIotaRat : ∀ (Φ : MatrixTestFunction n F) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ
        (coefficientIota (matrixCoefficient ρ ℓ v)) R)
    (hFE : ∀ (s : ℂ) (Φ : fourierRegularMatrixTests (n + 1) ψ ν hsd),
      fourierRegularInverseTransposeZetaOperator F ρ hι.1.1 ψ ν hsd s Φ =
        ((c : ℂ) * spectralPoint qF s ^ k) •
          fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ)
    (Φ : MatrixTestFunction n F) (v : V) :
    RationalReflection.subst
        (spectralReflectionUnit (Nat.zero_lt_one.trans
          (⟨⟩ : LocalFieldData F).residueCardinality_gt_one))
        (iotaFourierMatrixCoefficientRationalPairing F ψ ν hsd ρ ℓ hIotaRat Φ v) =
      laurentToRatFunc (laurentMonomialUnit (shiftedMatrixMonomialUnit F n c k) k :
        LaurentCoefficients) * matrixCoefficientRationalPairing F ρ ℓ hRat Φ v := by
  let B := reflectedIotaFourierMatrixCoefficientRationalPairing F ψ ν hsd ρ ℓ hIotaRat
  let M := laurentToRatFunc
    (laurentMonomialUnit (shiftedMatrixMonomialUnit F n c k) k : LaurentCoefficients)
  let D := (matrixCoefficientRationalPairing F ρ ℓ hRat).compr₂
    (LinearMap.mulLeft ℂ M)
  have heq : B = D := by
    apply matrixPairing_eq_of_fourierRegular F ψ ν hsd ρ hρ hi hn hι B D
    · exact reflectedIotaFourierMatrixCoefficientRationalPairing_translate
        F ψ ν hsd ρ ℓ hIotaRat
    · intro g hg Ψ w
      change M * matrixCoefficientRationalPairing F ρ ℓ hRat
        (rectangularTranslate g Ψ) w =
          M * matrixCoefficientRationalPairing F ρ ℓ hRat Ψ (ρ g⁻¹ w)
      rw [matrixCoefficientRationalPairing_translate F ρ ℓ hRat g hg]
    · apply LinearMap.ext
      intro Ψ
      apply LinearMap.ext
      intro w
      exact matrixRationalPairing_identity_of_fourierRegular_operator
        F ρ hρ.1.1 hι.1.1 ψ ν hsd c k ℓ hRat hIotaRat Ψ (fun s => hFE s Ψ) w
  exact congrArg (fun T => T Φ v) heq

/-- For arbitrary full-matrix tests and a fixed coefficient functional, the
same shifted monomial gives the normalized equation for all supplied actual
original and Fourier-dual rational values. -/
theorem normalizedFunctionalEquation_of_supercuspidal_fourierRegular_operator
    (hn : 0 < n)
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
    (hρ : IsSupercuspidal ρ) (hi : ρ.IsIrreducible)
    (hι : IsSupercuspidal (ρ.comp (inverseTranspose (n + 1) F).toMonoidHom))
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (c : ℂˣ) (k : ℤ)
    (ℓ : Module.Dual ℂ V)
    (hRat : ∀ (Φ : MatrixTestFunction n F) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ (matrixCoefficient ρ ℓ v) R)
    (hIotaRat : ∀ (Φ : MatrixTestFunction n F) (v : V),
      ∃ R, HasShiftedRationalValue qF abvF μF Φ
        (coefficientIota (matrixCoefficient ρ ℓ v)) R)
    (hFE : ∀ (s : ℂ) (Φ : fourierRegularMatrixTests (n + 1) ψ ν hsd),
      fourierRegularInverseTransposeZetaOperator F ρ hι.1.1 ψ ν hsd s Φ =
        ((c : ℂ) * spectralPoint qF s ^ k) •
          fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ)
    (Φ : MatrixTestFunction n F) (v : V) (R RDual : RationalFunctions)
    (hR : HasShiftedRationalValue qF abvF μF Φ (matrixCoefficient ρ ℓ v) R)
    (hD : HasShiftedRationalValue qF abvF μF
      (rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ)
      (coefficientIota (matrixCoefficient ρ ℓ v)) RDual) :
    NormalizedFunctionalEquation qF 1 1 1
      (shiftedMatrixMonomialUnit F n c k) 0 k R RDual := by
  have hid := matrixRationalPairing_identity_of_supercuspidal_fourierRegular_operator
    F hn ρ hρ hi hι ψ ν hsd c k ℓ hRat hIotaRat hFE Φ v
  have hBR := (matrixCoefficientRationalPairing_spec F ρ ℓ hRat Φ v).2.unique
    (⟨⟩ : LocalFieldData F).residueCardinality_gt_one hR.2
  have hDR := (iotaFourierMatrixCoefficientRationalPairing_spec
    F ψ ν hsd ρ ℓ hIotaRat Φ v).2.unique
      (⟨⟩ : LocalFieldData F).residueCardinality_gt_one hD.2
  rw [hBR, hDR] at hid
  exact Langlands.GodementJacquet.normalizedFunctionalEquation_of_monomial_rational_identity
    (⟨⟩ : LocalFieldData F).residueCardinality_gt_one hid

end Langlands.AllField.GodementJacquet.Padic
