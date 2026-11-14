import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonModelDataConvergence
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonRawConvergence
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylTransport
/-! Raw original and inverse-transpose bounds from matrix data on the actual model. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairGammaFactor QuotientHaarExistenceStatement RawModelIotaMatrixConvergence TorusCoefficientEnvelope UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement biSmooth_matrixDiagonal_convergesOnRight boundedDiagonalNormIntegrand boundedDiagonalNormIntegrand_convergesOnRight boundedDiagonalNormIntegrand_le_matrixDiagonal boxDiagonalLocalField boxDiagonalTopology boxDiagonalUnitsBorel boxDiagonalUnitsMeasurable boxDiagonalValuativeRel coefficientModelEvaluation_coefficient diagonalBorelDensity diagonalConj_map diagonalSliceWeight diagonalSliceWeight_nonneg enorm_weightedCoefficient_sub_natCast exists_uniform_matrixUnipotentNormSlice_bound glCoefficientModel_isOfWhittakerType integrable_biSmooth_matrixDiagonalIntegrand integrable_diagonalUnits_of_principalFixed isClopen_matrixNormBox isCompact_matrixNormBox lintegral_iwasawa_diagonalBorelDensity lintegral_norm_matrixIntegrand_iwasawa matrixComparisonModelsTopology matrixConvergesOnRight_inverseTransposePullback matrixConvergesOnRight_of_torusEnvelope matrixDiagonalIntegrand matrixIntegrand_exists_principalFixed matrixNormBox matrixNormBoxTest matrixNormBoxTest_diagonal_of_le matrixUnipotentNormSlice measurable_biSmooth_matrixIntegrand measurable_boundedDiagonalNormIntegrand measure_diagonalUnits_preimage_principalLevel_le_one modelDataLocalField modelDataTopology modelDataValuativeRel normalizedAbs_det_of_mem_integralSubgroup normalizedAbsoluteValue normalizedAbsoluteValue_apply rawMatrixGLBorel rawMatrixGLMeasurable rawMatrixLocalField rawMatrixNBorel rawMatrixNMeasurable rawMatrixSecondCountable rawMatrixT2 rawMatrixTopology rawMatrixUnitsBorel rawMatrixUnitsMeasurable rawMatrixUnitsSecondCountable rawMatrixValuativeRel rawModelIotaMatrixConvergence_of_modelIota singleton_modulus_real smoothDiagonalGLBorel smoothDiagonalGLLocallyCompact smoothDiagonalGLMeasurable smoothDiagonalGLSecondCountable smoothDiagonalLocalField smoothDiagonalSecondCountable smoothDiagonalT2 smoothDiagonalTopology smoothDiagonalUnitsBorel smoothDiagonalUnitsMeasurable smoothDiagonalUnitsSecondCountable smoothDiagonalValuativeRel smoothTorusGLBorel smoothTorusGLMeasurable smoothTorusLocalField smoothTorusTopology smoothTorusValuativeRel torusCoefficientEnvelope_of_smooth torusEnvelopeLocalField torusEnvelopeTopology torusEnvelopeValuation unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel whittakerCoefficientIota_matrixConvergesOnRight_of_iota whittakerCoefficient_matrixConvergesOnRight_of_matrix
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Topology
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.Conductor
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet
open Langlands.HarmonicAnalysis hiding padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open scoped ENNReal NNReal

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
  (ℓ : glFunctionals ψ n σ)
  (w : (glCoefficientModel ψ n σ ℓ).toSubmodule)

/-- The corresponding genuine raw inverse-transpose matrix bound. -/
def RawModelIotaMatrixConvergence : Prop :=
  ∀ Φ : MatrixTestFunction n F, ∃ b : ℝ, ∀ s : ℂ, b < s.re →
    Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ s (coefficientIota (glModelFunction ψ n σ ℓ w))

/-- Evaluation on the actual image realizes its original model function
as an actual coefficient, with no equivalence from the original carrier. -/
theorem coefficientModelEvaluation_coefficient :
    (fun g => (coefficientModelEvaluation σ ℓ).val
      (glModelRepresentation ψ n σ ℓ g w)) = glModelFunction ψ n σ ℓ w := by
  funext g
  change w.val.val (1 * g) = w.val.val g
  rw [one_mul]

/-- Raw inverse-transpose convergence for a coefficient of an abstract
smooth representation, before specializing to a coefficient-model carrier. -/
theorem whittakerCoefficientIota_matrixConvergesOnRight_of_iota
    (hσ : IsSmooth σ) (v : V)
    (hIota : Langlands.AllField.GodementJacquet.Padic.IotaMatrixConvergesOnRight F σ)
    (Φ : MatrixTestFunction n F) :
    ∃ b : ℝ, ∀ s : ℂ, b < s.re → Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ s
      (coefficientIota (fun g => ℓ.val (σ g v))) := by
  have hM := matrixConvergesOnRight_inverseTransposePullback F σ hIota
  obtain ⟨b, hb⟩ := whittakerCoefficient_matrixConvergesOnRight_of_matrix F (ψ.scale (-1))
    (inverseTransposePullback σ) (inverseTransposePullback_isSmooth σ hσ)
    (firstDualFunctional ψ σ ℓ) v hM (matrixWeylTranslate n Φ)
  refine ⟨b, fun s hs => ?_⟩
  apply (Langlands.AllField.GodementJacquet.Padic.matrixConverges_weylTranslate_dualFunction_iff F Φ s _).mp
  refine (hb s hs).congr
    (g := matrixIntegrand abv (matrixWeylTranslate n Φ) s
      (dualFunction n (fun g => ℓ.val (σ g v))))
    (Filter.Eventually.of_forall fun g => ?_)
  exact congrArg (fun z : ℂ => (matrixWeylTranslate n Φ) g.val * z *
    determinantWeight abv g s) (congrFun (dualFunction_coefficient ψ σ ℓ v) g).symm

/-- Transformed matrix bounds on the actual model give raw convergence of
its original inverse-transpose function for every full-matrix test. -/
theorem rawModelIotaMatrixConvergence_of_modelIota (hσ : IsSmooth σ)
    (hIota : Langlands.AllField.GodementJacquet.Padic.IotaMatrixConvergesOnRight F
      (V := (glCoefficientModel ψ n σ ℓ).toSubmodule) (glModelRepresentation ψ n σ ℓ)) :
    RawModelIotaMatrixConvergence F ψ σ ℓ w := by
  intro Φ
  obtain ⟨b, hb⟩ := @whittakerCoefficientIota_matrixConvergesOnRight_of_iota
    F _ _ _ _ n (glCoefficientModel ψ n σ ℓ).toSubmodule inferInstance inferInstance ψ
    (glModelRepresentation ψ n σ ℓ) (coefficientModelEvaluation σ ℓ)
    (glModel_isSmooth ψ n σ hσ ℓ) w hIota Φ
  refine ⟨b, fun s hs => ?_⟩
  refine (hb s hs).congr
    (g := matrixIntegrand abv Φ s (coefficientIota (glModelFunction ψ n σ ℓ w)))
    (Filter.Eventually.of_forall fun g => ?_)
  exact congrArg (fun z : ℂ => Φ g.val * z * determinantWeight abv g s)
    (congrFun (coefficientModelEvaluation_coefficient F ψ σ ℓ w)
      (inverseTranspose (n + 1) F g))

end Langlands.AllField.RankinSelberg
