import Langlands.Representation.GodementJacquet.TateScalarFunctionalEquation
import Langlands.AllField.LocalFactor.ResidueReflection
import Langlands.AllField.Representation.GodementJacquet.TateScalarMellin
import Langlands.AllField.Representation.GodementJacquet.TateScalarTransport
import Langlands.AllField.Representation.RankinSelberg.EqualRankFunctionalEquationProof
import Langlands.AllField.Representation.RankinSelberg.RankOneGammaTwistStatement
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonModels
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonZero
import Langlands.AllField.Representation.RankinSelberg.RankOneWhittakerTypeProof
/-! Scalar Tate functional equation from the independent equal-rank theorem. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding scalarMellinAnalyticData_finiteFunction
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding CentralBilinearVanishingStatement EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankContinuedFormsStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankGammaExistenceStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankTrilinearMirabolicPrerequisites EqualRankTrilinearPrerequisites EqualRankTrilinearUniquenessStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneCharacterReductionStatement RankOneGammaTwistStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement centralBilinearVanishing centralSpectralElement centralSpectralElement_det_abs centralSpectralElement_mem_center continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinantWeight_centralSpectralElement diagonalConj_map disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankContinuedForms equalRankFrobenius equalRankFunctionalEquation equalRankGammaExistence equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankTrilinearPrerequisites_of_mirabolic equalRankTrilinearUniqueness equalRankTrilinearUniqueness_of_mirabolic_prerequisites equalRankTrilinearUniqueness_of_prerequisites equalRankUnitValue finiteFunctionMellin finiteFunctionShellSeries glCoefficientModel_isOfWhittakerType hasEqualRankCompactTest_of_kirillov iUnion_determinantSlice inverseUniformizer_normalizedAbsoluteValue isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit matrixComparisonModelsTopology measurableSet_determinantSlice mem_determinantSlice mirabolic_exists_exception_length_le_one mirabolic_pair_control_of_statements mirabolic_shift_length_bound mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneMatrixWhittakerComparison_zero rankOneWhittakerType rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicCompactTwistedPairingStatement MirabolicFiniteLengthStatement MirabolicFunctionalMultiplicityStatement MirabolicTwistedPairingRigidityStatement MirabolicUnitTestStatement UnipotentOrbitStatement compactLocalization exists_compactOpen_glCoefficientRightStabilizer mirabolicCompactTwistedPairing mirabolicFiniteLength mirabolicFunctionalMultiplicity mirabolicTwistedPairingRigidity mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport unipotentOrbit
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF

section Coordinates



end Coordinates

section Fourier


end Fourier

namespace Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 integrable_tateScalarEquiv_iff integral_tateScalarEquiv iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues tateCharacterModelOne_at_one tateDualEqualRankIntegral_eq_scalar tateDualEqualRankIntegral_unit_eq_scalar tateDualEqualRankRationalValues_eq_scalar tateEqualRankIntegral_eq_scalar tateEqualRankIntegral_unit_eq_scalar tateEqualRankRationalValues_eq_scalar tateFEBorel tateFEGLBorel tateFEGLMeasurable tateFELocalField tateFEMeasurable tateFEQuotientBorel tateFEQuotientMeasurable tateFET2 tateFETopology tateFETotallyDisconnected tateFEUnipotentBorel tateFEUnipotentMeasurable tateFEUnitsBorel tateFEUnitsMeasurable tateFEValuativeRel tateScalarEquiv_measurePreserving tateScalarFunctionalEquation tateTransportGLBorel tateTransportGLLocallyCompact tateTransportGLMeasurable tateTransportGLSecondCountable tateTransportLocalField tateTransportTopology tateTransportUnitsBorel tateTransportUnitsMeasurable tateTransportValuation tateTrivialModelOne_at_one whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues scalarMellinAnalyticData_finiteFunction whittakerRationalValues
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance tateFET2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance tateFETotallyDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance tateFEMeasurable : MeasurableSpace F := borel _
local instance tateFEBorel : BorelSpace F := ⟨rfl⟩
local instance tateFEUnitsMeasurable : MeasurableSpace Fˣ := borel _
local instance tateFEUnitsBorel : BorelSpace Fˣ := ⟨rfl⟩
local instance tateFEGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance tateFEGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance tateFEUnipotentMeasurable (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance tateFEUnipotentBorel (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
local instance tateFEQuotientMeasurable : MeasurableSpace (LeftUnipotentQuotient 0 F) := borel _
local instance tateFEQuotientBorel : BorelSpace (LeftUnipotentQuotient 0 F) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
local notation "q" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))
local notation "μ" => localMultiplicativeHaar F

variable (ψ : UnitaryAdditiveCharacter F) (χ : Quasicharacter F)

local notation "πχ" => rankOneCharacter (χ : Fˣ →* ℂˣ)
local notation "π₁" => rankOneCharacter (1 : Fˣ →* ℂˣ)
local notation "ℓχ" => tateCharacterFunctional F ψ (χ : Fˣ →* ℂˣ)
local notation "ℓ₁" => rankOneTrivialInverseFunctional ψ

/-- Original model integrals are scalar Mellin integrals, with the two vector
coordinates absorbed into the test. -/
theorem tateEqualRankIntegral_eq_scalar
    (f : (coefficientModel πχ ℓχ).toSubmodule)
    (f' : (coefficientModel π₁ ℓ₁).toSubmodule)
    (Φ : SchwartzBruhat (Fin 1 → F)) (s : ℂ) :
    equalRankModelIntegral ψ abv (rankOneQuotientHaar F)
        πχ π₁ ℓχ ℓ₁ f f' Φ s =
      scalarMellinIntegral (⟨⟩ : LocalFieldData F).normalizedAbs μ
        (fun a => (χ a : ℂ)) 1
        ((f.val.val 1 * f'.val.val 1) • tateScalarRowTest F Φ) s := by
  unfold equalRankModelIntegral
  rw [equalRankIntegral_rankOneQuotientHaar, ← integral_tateScalarEquiv F]
  apply integral_congr_ae
  filter_upwards [] with a
  have hdet : determinant (tateScalarEquiv F a) = a :=
    (tateScalarEquiv F).symm_apply_apply a
  have hdetval : (tateScalarEquiv F a).val.det = (a : F) :=
    congrArg Units.val hdet
  have hrow : lastRow (tateScalarEquiv F a) = fun _ => (a : F) := by
    funext i
    fin_cases i
    simp [lastRow, tateScalarEquiv, scalar, Matrix.GeneralLinearGroup.coe_scalar]
  rw [equalRankFunction,
    tateCharacterModel_apply F ψ (χ : Fˣ →* ℂˣ) f _,
    rankOneTrivialModel_constant ψ ℓ₁ f' _]
  simp only [scalarMellinIntegrand, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    tateScalarRowTest_apply, Nat.cast_one, one_mul, determinantWeight, hdet, hdetval, hrow]
  change (χ a : ℂ) * f.val.val 1 * f'.val.val 1 * Φ (fun _ => (a : F)) *
    ((⟨⟩ : LocalFieldData F).normalizedAbs (a : F) : ℂ) ^ s = _
  ring

/-- The transformed model integrals use the inverse multiplicative character. -/
theorem tateDualEqualRankIntegral_eq_scalar
    (f : (coefficientModel πχ ℓχ).toSubmodule)
    (f' : (coefficientModel π₁ ℓ₁).toSubmodule)
    (Φ : SchwartzBruhat (Fin 1 → F)) (s : ℂ) :
    dualEqualRankModelIntegral ψ abv (rankOneQuotientHaar F)
        πχ π₁ ℓχ ℓ₁ f f' Φ s =
      scalarMellinIntegral (⟨⟩ : LocalFieldData F).normalizedAbs μ
        (fun a => ((χ a)⁻¹ : ℂ)) 1
        ((f.val.val 1 * f'.val.val 1) • tateScalarRowTest F Φ) s := by
  unfold dualEqualRankModelIntegral
  rw [equalRankIntegral_rankOneQuotientHaar, ← integral_tateScalarEquiv F]
  apply integral_congr_ae
  filter_upwards [] with a
  have hdet : determinant (tateScalarEquiv F a) = a :=
    (tateScalarEquiv F).symm_apply_apply a
  have hdetval : (tateScalarEquiv F a).val.det = (a : F) :=
    congrArg Units.val hdet
  have hrow : lastRow (tateScalarEquiv F a) = fun _ => (a : F) := by
    funext i
    fin_cases i
    simp [lastRow, tateScalarEquiv, scalar, Matrix.GeneralLinearGroup.coe_scalar]
  rw [equalRankFunction, firstDualFunction_apply, secondDualFunction_apply,
    weylLong_rankOne_eq_one, one_mul,
    tateCharacterModel_apply F ψ (χ : Fˣ →* ℂˣ) f _,
    rankOneTrivialModel_constant ψ ℓ₁ f' _,
    RankOneGammaTwist.determinant_inverseTranspose, hdet]
  simp only [scalarMellinIntegrand, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
    tateScalarRowTest_apply, Nat.cast_one, one_mul, determinantWeight, hdetval, hrow,
    map_inv, Units.val_inv_eq_inv_val]
  change ((χ a)⁻¹ : ℂ) * f.val.val 1 * f'.val.val 1 * Φ (fun _ => (a : F)) *
    ((⟨⟩ : LocalFieldData F).normalizedAbs (a : F) : ℂ) ^ s = _
  ring

/-- The coefficient of the unit vector is normalized at the identity. -/
@[simp] theorem tateCharacterModelOne_at_one :
    (modelMap πχ ℓχ (1 : ℂ)).val.val 1 = 1 := by
  change (πχ 1) (1 : ℂ) = 1
  simp

/-- The trivial coefficient of the unit vector is normalized at the identity. -/
@[simp] theorem tateTrivialModelOne_at_one :
    (modelMap π₁ ℓ₁ (1 : ℂ)).val.val 1 = 1 := by
  change (π₁ 1) (1 : ℂ) = 1
  simp

/-- At unit model vectors, only the row-to-scalar test transport remains. -/
theorem tateEqualRankIntegral_unit_eq_scalar
    (Φ : SchwartzBruhat (Fin 1 → F)) :
    equalRankModelIntegral ψ abv (rankOneQuotientHaar F)
        πχ π₁ ℓχ ℓ₁ (modelMap πχ ℓχ 1) (modelMap π₁ ℓ₁ 1) Φ =
      scalarMellinIntegral (⟨⟩ : LocalFieldData F).normalizedAbs μ
        (fun a => (χ a : ℂ)) 1 (tateScalarRowTest F Φ) := by
  funext s
  simpa only [tateCharacterModelOne_at_one, tateTrivialModelOne_at_one,
    one_mul, one_smul] using
    tateEqualRankIntegral_eq_scalar F ψ χ (modelMap πχ ℓχ 1) (modelMap π₁ ℓ₁ 1) Φ s

/-- The unit dual model vectors give exactly the inverse-character Mellin test. -/
theorem tateDualEqualRankIntegral_unit_eq_scalar
    (Φ : SchwartzBruhat (Fin 1 → F)) :
    dualEqualRankModelIntegral ψ abv (rankOneQuotientHaar F)
        πχ π₁ ℓχ ℓ₁ (modelMap πχ ℓχ 1) (modelMap π₁ ℓ₁ 1) Φ =
      scalarMellinIntegral (⟨⟩ : LocalFieldData F).normalizedAbs μ
        (fun a => ((χ a)⁻¹ : ℂ)) 1 (tateScalarRowTest F Φ) := by
  funext s
  simpa only [tateCharacterModelOne_at_one, tateTrivialModelOne_at_one,
    one_mul, one_smul] using
    tateDualEqualRankIntegral_eq_scalar F ψ χ (modelMap πχ ℓχ 1) (modelMap π₁ ℓ₁ 1) Φ s

/-- Equality of the complete original rational-value families. -/
theorem tateEqualRankRationalValues_eq_scalar :
    equalRankRationalValues q ψ abv (rankOneQuotientHaar F) πχ π₁ ℓχ ℓ₁ =
      scalarMellinRationalValues q (⟨⟩ : LocalFieldData F).normalizedAbs μ
        (fun a => (χ a : ℂ)) 1 := by
  ext R
  constructor
  · rintro ⟨f, f', Φ, hR⟩
    refine ⟨(f.val.val 1 * f'.val.val 1) • tateScalarRowTest F Φ, ?_⟩
    have heq := funext (tateEqualRankIntegral_eq_scalar F ψ χ f f' Φ)
    rwa [heq] at hR
  · rintro ⟨Φ, hR⟩
    refine ⟨modelMap πχ ℓχ 1, modelMap π₁ ℓ₁ 1, tateRowTest F Φ, ?_⟩
    rwa [tateEqualRankIntegral_unit_eq_scalar, tateScalarRowTest_tateRowTest]

/-- Equality of the complete dual rational-value families. -/
theorem tateDualEqualRankRationalValues_eq_scalar :
    dualEqualRankRationalValues q ψ abv (rankOneQuotientHaar F) πχ π₁ ℓχ ℓ₁ =
      scalarMellinRationalValues q (⟨⟩ : LocalFieldData F).normalizedAbs μ
        (fun a => ((χ a)⁻¹ : ℂ)) 1 := by
  ext R
  constructor
  · rintro ⟨f, f', Φ, hR⟩
    refine ⟨(f.val.val 1 * f'.val.val 1) • tateScalarRowTest F Φ, ?_⟩
    have heq := funext (tateDualEqualRankIntegral_eq_scalar F ψ χ f f' Φ)
    rwa [heq] at hR
  · rintro ⟨Φ, hR⟩
    refine ⟨modelMap πχ ℓχ 1, modelMap π₁ ℓ₁ 1, tateRowTest F Φ, ?_⟩
    rwa [tateDualEqualRankIntegral_unit_eq_scalar, tateScalarRowTest_tateRowTest]

/-- The scalar Tate functional equation for the exact supplied self-dual Haar
measure. The epsilon constant and exponent are chosen before every scalar test;
the equation holds for every pair of its actual rational continuations. -/
theorem tateScalarFunctionalEquation
    (ν : AdditiveHaarMeasure F) (hν : IsSelfDual ψ ν)
    {P PDual : Polynomial ℂ}
    (hP : IsNormalizedGenerator
      (scalarMellinRationalValues q (⟨⟩ : LocalFieldData F).normalizedAbs μ
        (fun a => (χ a : ℂ)) 1) P)
    (hPDual : IsNormalizedGenerator
      (scalarMellinRationalValues q (⟨⟩ : LocalFieldData F).normalizedAbs μ
        (fun a => ((χ a)⁻¹ : ℂ)) 1) PDual) :
    ∃ (c : ℂˣ) (a : ℤ), ∀ Φ : SchwartzBruhat F,
      ∃ Φhat : SchwartzBruhat F,
        (∀ y, Integrable (fun x => ψ.complex (x * y) * Φ x) ν.measure ∧
          Φhat y = fourierIntegral ψ ν Φ y) ∧
        ∀ R RDual : RationalFunctions,
          HasRationalContinuation q
            (scalarMellinIntegral (⟨⟩ : LocalFieldData F).normalizedAbs μ
              (fun x => (χ x : ℂ)) 1 Φ) R →
          HasRationalContinuation q
            (scalarMellinIntegral (⟨⟩ : LocalFieldData F).normalizedAbs μ
              (fun x => ((χ x)⁻¹ : ℂ)) 1 Φhat) RDual →
          NormalizedFunctionalEquation q P PDual 1 c 0 a R RDual := by
  have hχ := rankOneCharacter_isOfWhittakerType F ψ χ
  have h₁ : IsOfWhittakerType 0 (inverseStandardCharacter ψ 0) π₁ := by
    apply (isOfWhittakerType_standard_iff_inverse ψ _).mp
    exact rankOneCharacter_isOfWhittakerType F ψ 1
  let := unipotentHaar_isMulRightInvariant F 0
  obtain ⟨ζ, c, a, Q, QDual, -, hQ, hQDual, hFE⟩ :=
    equalRankFunctionalEquation.{uF, 0, 0} F (⟨⟩ : LocalFieldData F) 0 ψ
      (rankOneQuotientHaar F) (rankOneQuotientHaar_isCompatible F)
      ν hν ℂ ℂ πχ π₁ hχ h₁ ℓχ ℓ₁
      (tateCharacterFunctional_ne_zero F ψ (χ : Fˣ →* ℂˣ))
      (rankOneTrivialInverseFunctional_ne_zero ψ)
  rw [tateEqualRankRationalValues_eq_scalar] at hQ
  rw [tateDualEqualRankRationalValues_eq_scalar] at hQDual
  obtain rfl := IsNormalizedGenerator.unique hQ hP
  obtain rfl := IsNormalizedGenerator.unique hQDual hPDual
  refine ⟨c, a, fun Φ => ?_⟩
  obtain ⟨Ψ, R₀, RDual₀, hFourier, hR₀, hRDual₀, hNorm⟩ :=
    hFE (modelMap πχ ℓχ 1) (modelMap π₁ ℓ₁ 1) (tateRowTest F Φ)
  rw [tateEqualRankIntegral_unit_eq_scalar, tateScalarRowTest_tateRowTest] at hR₀
  rw [tateDualEqualRankIntegral_unit_eq_scalar] at hRDual₀
  refine ⟨tateScalarRowTest F Ψ,
    tateScalarFourierPair_of_row ψ ν Φ Ψ hFourier, ?_⟩
  intro R RDual hR hRDual
  obtain rfl := hR.unique (⟨⟩ : LocalFieldData F).residueCardinality_gt_one hR₀
  obtain rfl := hRDual.unique (⟨⟩ : LocalFieldData F).residueCardinality_gt_one hRDual₀
  simpa only [NormalizedFunctionalEquation, pow_zero] using hNorm

end Padic

end Langlands.AllField.GodementJacquet
