import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPairedComparison
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxConvergence
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPositiveAssembly
/-! # Assembly from a concrete same-coefficient paired matrix comparison

The actual matrix premise and proved block continuations remove all analytic
inputs from the assembly boundary. What remains is the simultaneous original
and genuine-dual comparison with one actual coefficient and one nonzero scalar.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput PairedMatrixBlockComparison QuotientHaarExistenceStatement RankOneCharacterReductionStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map diagonal_abs_bound diagonal_abs_last exists_rankOneCutoff exists_rankOneEmbedding_support glCoefficientModel_isOfWhittakerType isEqualRankLPolynomial_characterChange_normalized isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit matrixComparisonModelsTopology matrixComparisonPositiveBorel matrixComparisonPositiveDisconnected matrixComparisonPositiveGLBorel matrixComparisonPositiveGLMeasurable matrixComparisonPositiveLocalField matrixComparisonPositiveMeasurable matrixComparisonPositiveQuotientBorel matrixComparisonPositiveQuotientMeasurable matrixComparisonPositiveT2 matrixComparisonPositiveTopology matrixComparisonPositiveUnipotentBorel matrixComparisonPositiveUnipotentMeasurable matrixComparisonPositiveValuation normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType pairedComparisonGLBorel pairedComparisonGLMeasurable pairedComparisonLocalField pairedComparisonQuotientBorel pairedComparisonQuotientMeasurable pairedComparisonScalarMeasurable pairedComparisonTopology pairedComparisonUnipotentBorel pairedComparisonUnipotentMeasurable pairedComparisonValuativeRel rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaFactor_of_blockZero_one rankOneGammaFactor_of_normalized_blockZero_one rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rankOne_blockZero_exists_ne_zero singleton_modulus_real unequalRankCompactSupport unequalRankFiniteExpansion unequalRankGammaPropagation unequalRankIwasawaSupport unequalRankUnitSpan zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularHaarScaling padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV

section Padic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance pairedComparisonScalarMeasurable : MeasurableSpace F := borel _
local instance pairedComparisonGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance pairedComparisonGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance pairedComparisonUnipotentMeasurable :
    MeasurableSpace (upperUnipotent (0 + 1) F) := borel _
local instance pairedComparisonUnipotentBorel :
    BorelSpace (upperUnipotent (0 + 1) F) := ⟨rfl⟩
local instance pairedComparisonQuotientMeasurable :
    MeasurableSpace (LeftUnipotentQuotient 0 F) := borel _
local instance pairedComparisonQuotientBorel :
    BorelSpace (LeftUnipotentQuotient 0 F) := ⟨rfl⟩

variable {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
  (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
  (ℓ : glFunctionals ψ r σ)

/-- The concrete paired extraction boundary: one actual original coefficient,
one test and one common nonzero scalar compare to the literal original and
genuine complementary-dual block-zero integrals on right half-planes. -/
def PairedMatrixBlockComparison (hrpos : 0 < r) : Prop :=
  ∀ w : (glCoefficientModel ψ r σ ℓ).toSubmodule,
    ∃ Φ : GodementJacquet.MatrixTestFunction r F,
      ∃ f : GodementJacquet.biSmoothMatrixCoefficients
        (V := (glCoefficientModel ψ r σ ℓ).toSubmodule) (glModelRepresentation ψ r σ ℓ),
      ∃ C : ℂ, C ≠ 0 ∧
        (∃ b : ℝ, ∀ s : ℂ, b < s.re →
          GodementJacquet.matrixIntegral (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
              (generalLinearHaar F r) Φ (s + GodementJacquet.jpssShift r) f.val =
            C * unequalRankIntegralAt 0 (r - 0 - 1) (by omega) ψ
              (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
              (unipotentQuotientHaar F 0) (rectangularMeasure ν 0 (0 + 1))
              w.val (rankOneTrivialModelOne ψ).val s) ∧
        ∀ ΦHat : GodementJacquet.MatrixTestFunction r F,
          Langlands.AllField.GodementJacquet.Padic.MatrixFourierPair F ψ ν Φ ΦHat →
          ∃ b : ℝ, ∀ s : ℂ, b < s.re →
            GodementJacquet.matrixIntegral (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
                (generalLinearHaar F r) ΦHat (s + GodementJacquet.jpssShift r)
                (GodementJacquet.coefficientIota f.val) =
              C * dualUnequalRankModelIntegralAt hrpos 0 (r - 0 - 1) (by omega) ψ
                (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
                (unipotentQuotientHaar F 0) ν σ
                (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ (rankOneTrivialInverseFunctional ψ)
                w (rankOneTrivialModelOne ψ) s

end Padic

end Langlands.AllField.RankinSelberg
