import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonHaarShear
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedGLFourier
import Langlands.AllField.Representation.Shahidi.Induction
/-! Exact subgroup Haar shear and the actual signed original Fourier kernel. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map exists_rankOneCutoff exists_rankOneEmbedding_support lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneModelValues_subset_whittakerRationalValues singleton_modulus_real unequalRankFiniteExpansion zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularFourierIntegral_exchange_left padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest
open Langlands.AllField.Whittaker
open Langlands.RankinSelberg.CompactWhittakerSynthesis hiding firstColumnFrame_mem_range_of_mem_box instValuativeRelCarrier_1 integrable_signedUnipotentMatrixFourierDualKernel integrable_signedUnipotentMatrixFourierOriginalKernel integral_signedUnipotentMatrixFourierKernel_fixed signedOrbitBorelSpace signedOrbitGLSecondCountable signedOrbitLocalField signedOrbitMeasurableSpace signedOrbitNBorelSpace signedOrbitNLocallyCompact signedOrbitNMeasurableSpace signedOrbitNSecondCountable signedOrbitSecondCountable signedOrbitT2 signedOrbitTopology signedOrbitTotallyDisconnected signedOrbitValuativeRel signedUnipotentMatrixFourier_exchange
open Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis

universe uG uF

section General


end General

namespace GLDeterminantDensity
open Langlands.RankinSelberg.GLDeterminantDensity hiding forwardWeight_eq_determinantWeight generalLinear_signedUnipotentMatrixFourier_exchange glFourierGLBorelSpace glFourierGLMeasurableSpace glFourierLocalField glFourierMeasurableSpace glFourierTopology glFourierValuativeRel haarShearBorel haarShearGLBorel haarShearGLLocallyCompact haarShearGLMeasurable haarShearGLSecondCountable haarShearLocalField haarShearMeasurable haarShearNBorel haarShearNLocallyCompact haarShearNMeasurable haarShearNSecondCountable haarShearT2 haarShearTopology haarShearTotallyDisconnected haarShearValuativeRel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instLocallyCompactSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instSecondCountableTopologyCarrier instSecondCountableTopologyGeneralLinearHAddNatOfNatCarrier instSigmaCompactSpaceCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_generalLinearHaar_natWeight_iff integrable_generalLinear_signedUnipotentMatrixFourierDualKernel integrable_generalLinear_signedUnipotentMatrixFourierOriginalKernel integrable_generalLinear_signedUnipotentMatrixFourierShearedKernel integrable_prod_generalLinearHaar_natWeight_iff integrable_prod_generalLinearHaar_natWeight_iff_full integral_generalLinearHaar_natWeight integral_generalLinear_signedUnipotentMatrixFourierDualKernel integral_generalLinear_signedUnipotentMatrixFourierOriginalKernel integral_generalLinear_signedUnipotentMatrixFourierShearedKernel integral_prod_generalLinearHaar_natWeight integral_prod_generalLinearHaar_natWeight_full padic_exists_weightedRestriction_eq_generalLinearHaar padic_weightedRestriction_isHaar rectangularHaarScalar rectangularHaarScalar_pos rectangularMeasure_ae_det_ne_zero rectangularMeasure_restrict_generalLinear signedGLFourierBorelSpace signedGLFourierGLBorelSpace signedGLFourierGLMeasurableSpace signedGLFourierGLSecondCountable signedGLFourierLocalField signedGLFourierMeasurableSpace signedGLFourierNBorelSpace signedGLFourierNLocallyCompact signedGLFourierNMeasurableSpace signedGLFourierNSecondCountable signedGLFourierT2 signedGLFourierTopology signedGLFourierTotallyDisconnected signedGLFourierValuativeRel signedUnipotentGeneralLinearFourierDualKernel signedUnipotentGeneralLinearFourierOriginalKernel signedUnipotentGeneralLinearFourierOriginalKernel_shear signedUnipotentGeneralLinearFourierShearedKernel singularNullBorelSpace singularNullLocalField singularNullMeasurableSpace singularNullPuncturedNhds singularNullSecondCountable singularNullSigmaCompact singularNullT2 singularNullTopology singularNullValuativeRel weightedRestriction_eq_rectangularHaarScalar
open Langlands.AllField.RankinSelberg.GLDeterminantDensity
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map exists_rankOneCutoff exists_rankOneEmbedding_support lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneModelValues_subset_whittakerRationalValues singleton_modulus_real unequalRankFiniteExpansion zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance haarShearT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance haarShearMeasurable : MeasurableSpace F := borel _
local instance haarShearBorel : BorelSpace F := ⟨rfl⟩
local instance haarShearGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance haarShearGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance haarShearGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace (n + 1)
local instance haarShearGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology (n + 1)
local instance haarShearNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).upperUnipotentLocallyCompactSpace (n + 1)
local instance haarShearNSecondCountable (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance haarShearNMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance haarShearNBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩

local instance haarShearTotallyDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

/-- The signed original kernel after the exact substitution `X = u g`. -/
def signedUnipotentGeneralLinearFourierShearedKernel
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (z : upperUnipotent (n + 1) F ×
      Langlands.GeneralLinear (n + 1) F) : ℂ :=
  determinantWeight abv z.2 (n + 1 : ℕ) *
    ((inverseStandardCharacter ψ n z.1 : ℂ) * Φ (z.1.val * z.2).val *
      rectangularFourierIntegral ψ ν Ψ (rankOneSignedWeyl n * z.2).val)

/-- Unipotent determinant one removes the weight change, and the true
group substitution cancels `u⁻¹ u` in the signed Weyl Fourier argument. -/
theorem signedUnipotentGeneralLinearFourierOriginalKernel_shear
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (z : upperUnipotent (n + 1) F ×
      Langlands.GeneralLinear (n + 1) F) :
    signedUnipotentGeneralLinearFourierOriginalKernel F ψ ν n Φ Ψ
      (subgroupLeftHaarShear (upperUnipotent (n + 1) F)
        continuous_subtype_val.measurable z) =
      signedUnipotentGeneralLinearFourierShearedKernel F ψ ν n Φ Ψ z := by
  have hw : determinantWeight abv (z.1.val * z.2) (n + 1 : ℕ) =
      determinantWeight abv z.2 (n + 1 : ℕ) := by
    change (Shahidi.determinantPower abv (n + 1) (n + 1 : ℕ) (z.1.val * z.2) : ℂ) = _
    rw [map_mul, determinantPower_upperUnipotent, one_mul]
    rfl
  simp only [signedUnipotentGeneralLinearFourierOriginalKernel,
    signedUnipotentMatrixFourierOriginalKernel, subgroupLeftHaarShear_apply,
    signedUnipotentGeneralLinearFourierShearedKernel, hw]
  congr 3
  rw [← Units.val_mul, mul_assoc, inv_mul_cancel_left]

/-- Genuine product convergence transfers through the Haar shear. -/
theorem integrable_generalLinear_signedUnipotentMatrixFourierShearedKernel
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (hΦ : tsupport (Φ : _ → ℂ) ⊆
      Set.range (Units.val : Langlands.GeneralLinear (n + 1) F →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F)) :
    Integrable (signedUnipotentGeneralLinearFourierShearedKernel F ψ ν n Φ Ψ)
      ((unipotentHaar F n).prod (generalLinearHaar F n)) := by
  have hi := (integrable_subgroupLeftHaarShear_iff
    (upperUnipotent (n + 1) F) continuous_subtype_val.measurable
    (unipotentHaar F n) (generalLinearHaar F n)
    (signedUnipotentGeneralLinearFourierOriginalKernel F ψ ν n Φ Ψ)).2
    (integrable_generalLinear_signedUnipotentMatrixFourierOriginalKernel F ψ ν hsd n Φ Ψ hΦ)
  simpa only [signedUnipotentGeneralLinearFourierOriginalKernel_shear] using hi

/-- The original and sheared product integrals are exactly equal, including
as total integrals when no convergence premise is supplied. -/
theorem integral_generalLinear_signedUnipotentMatrixFourierShearedKernel
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F)) :
    (∫ z, signedUnipotentGeneralLinearFourierShearedKernel F ψ ν n Φ Ψ z
      ∂(unipotentHaar F n).prod (generalLinearHaar F n)) =
    ∫ z, signedUnipotentGeneralLinearFourierOriginalKernel F ψ ν n Φ Ψ z
      ∂(unipotentHaar F n).prod (generalLinearHaar F n) := by
  simpa only [signedUnipotentGeneralLinearFourierOriginalKernel_shear] using
    integral_subgroupLeftHaarShear
      (upperUnipotent (n + 1) F) continuous_subtype_val.measurable
      (unipotentHaar F n) (generalLinearHaar F n)
      (signedUnipotentGeneralLinearFourierOriginalKernel F ψ ν n Φ Ψ)

end GLDeterminantDensity
end Langlands.AllField.RankinSelberg
