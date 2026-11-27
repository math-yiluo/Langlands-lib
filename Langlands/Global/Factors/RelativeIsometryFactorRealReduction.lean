import Langlands.Global.RankinSelberg.EqualSemilocalEquationTCFromOrdinaryTests
import Langlands.Automorphic.AssociatedGammaFinal
import Langlands.Automorphic.AssociatedTemperedAssembly
import Langlands.Automorphic.StableTwistGammaMatchProof
import Langlands.ClassFieldTheory.Local.CommonClosureExistenceProof
import Langlands.Global.Factors.CuspidalArchimedeanParameterExistenceProof
import Langlands.Global.Factors.CuspidalPairLocalDataProof
import Langlands.Global.Factors.CuspidalPairPartialGammaGlobalReduction
import Langlands.Global.Factors.CuspidalSatakeBoundReduction
import Langlands.Global.Factors.RelativeIsometryFactorReduction
import Langlands.Global.RankinSelberg.ArchimedeanCentralSignProof
import Langlands.Global.RankinSelberg.ComplexOrdinaryNormalizedGenerationProof
import Langlands.Global.RankinSelberg.ComplexPlaceWhittakerRange
import Langlands.Global.RankinSelberg.EqualAnalyticProof
import Langlands.Global.RankinSelberg.EqualDualEulerFactorizationProof
import Langlands.Global.RankinSelberg.EqualEulerFactorizationProof
import Langlands.Global.RankinSelberg.EqualSemilocalFactorizationReduction
import Langlands.Global.RankinSelberg.EqualSemilocalReduction
import Langlands.Global.RankinSelberg.EqualUnfoldingProof
import Langlands.Global.RankinSelberg.InfiniteWhittakerSliceProof
import Langlands.Global.RankinSelberg.RealLocalUniformPositiveEqualContinuationProof
import Langlands.Global.RankinSelberg.RealPlaceContragredientReduction
import Langlands.Global.RankinSelberg.RealPlaceWhittakerRange
import Langlands.Global.RankinSelberg.RealStandardDualPairingProof
import Langlands.Global.RankinSelberg.RealStandardIntertwinerPairLProof
import Langlands.Global.RankinSelberg.RealStandardPairingReduction
import Langlands.Global.RankinSelberg.RealUnequalRankZeroOrdinary
import Langlands.Global.RankinSelberg.RealUniformContinuationReduction
import Langlands.Global.RankinSelberg.UnequalAnalyticProof
import Langlands.Global.RankinSelberg.UnequalDualEulerFactorizationProof
import Langlands.Global.RankinSelberg.UnequalEulerFactorizationProof
import Langlands.Global.RankinSelberg.UnequalSemilocalArchimedeanReduction
import Langlands.Global.RankinSelberg.UnequalUnfoldingProof
import Langlands.LocalFactor.NonabelianSystemExistsProof

/-! # Relative isometry factors from real archimedean tests -/

set_option autoImplicit false

universe uF uW uP uE

namespace Langlands.Global.PoleComparison

open ClassFieldTheory.Global.RelativeWeilGroup
open RankinSelbergGlobal HeckeFunctionalEquation
open scoped CategoryTheory.MonObj

private theorem realPlaceEquation_of_unequalContinuation
    (hUnequal : RealLocalUniformUnequalContinuationStatement) :
    RealPlaceFunctionalEquationStatement.{uF} :=
  realPlaceUniformContinuationReduction hUnequal realLocalUniformPositiveEqualContinuation
    (realPlaceContragredientPairLReduction Automorphic.cuspidalArchimedeanStandardIrreducible
      (realStandardPairingPairLReduction realStandardDualPairing realStandardIntertwinerPairL))

private theorem relativeIsometryFactor_of_archimedeanTheory
    (hTheory : ArchimedeanSemilocalTheoryStatement.{uF, uF}) :
    RelativeIsometryFactorStatement.{uF, uW, uP, uE} := by
  have hUnequal := unequalSemilocalArchimedeanReduction hTheory
  have hEqual := equalSemilocalReduction (equalSemilocalFactorization_of_archimedeanSemilocalTheory hTheory)
  have hPartial := cuspidalPairPartialGammaGlobalReduction
    UnequalAnalytic.unequalAnalyticStatement_proof unequalUnfoldingStatement_proof
    unequalEulerFactorization unequalDualEulerFactorization hUnequal
    EqualAnalytic.equalAnalyticStatement_proof equalUnfoldingStatement_proof
    equalEulerFactorization equalDualEulerFactorization hEqual
  have hCompleted := cuspidalPairCompletedEquation_of_satakeBound_of_partialGamma
    (cuspidalSatakeBoundReduction Automorphic.OperatorRealization.irreducibleCentralCharacter)
    hPartial
  have hEquation := cuspidalPairFunctionalEquationReduction cuspidalPairLocalData
    cuspidalArchimedeanParameterExistence hCompleted
  exact relativeIsometryFactorStatement_of_tempered
    (associatedTemperedFactor_of_gamma_and_existence
      (associatedGamma_of_inputs hEquation stableTwistPairGammaMatchStatement)
      LocalClassField.commonClosureReciprocityExistence
      (fun _ _ K eC => LocalFactor.NonabelianSystem.exists_system K eC))

/-- Real unequal-rank continuation and ordinary place tests with smaller group of rank at
least two imply determinant and pair-factor compatibility over arbitrary number fields. -/
def RelativeIsometryFactorRealReductionStatement : Prop :=
  RealLocalUniformUnequalContinuationStatement →
    RealUnequalOrdinaryPlaceTestsPositiveRankStatement.{uF} →
    RealEqualOrdinaryPlaceTestsPositiveRankStatement.{uF} →
    RelativeIsometryFactorStatement.{uF, uW, uP, uE}

/-- Supply the rank-one tests, complex-place theory and global functional equation from the
specified real inputs. -/
theorem relativeIsometryFactorStatement_of_realContinuation_and_tests :
    RelativeIsometryFactorRealReductionStatement.{uF, uW, uP, uE} := by
  intro hUnequal hOrdUnequal hOrdEqual
  have hReal := realPlaceEquation_of_unequalContinuation hUnequal
  have hComplexTests := complexOrdinaryPlaceTests_of_generation
    complexOrdinaryNormalizedGeneration complexWhittakerRestrictionOnto
  have hFactorization := archimedeanFactorizationOrdinaryReduction infiniteWhittakerSliceModel hReal
    (realUnequalOrdinaryPlaceTestsFromPositiveRank hOrdUnequal) hComplexTests.1
    hOrdEqual hComplexTests.2
  exact relativeIsometryFactor_of_archimedeanTheory
    ⟨⟨complexPlaceFunctionalEquation, hReal⟩, hFactorization, archimedeanCentralSign⟩

/-- Real ordinary normalized generation supplies both ordinary place-test hypotheses. -/
theorem relativeIsometryFactorStatement_of_realContinuation_and_generation
    (hUnequal : RealLocalUniformUnequalContinuationStatement)
    (hGeneration : RealOrdinaryNormalizedGenerationStatement) :
    RelativeIsometryFactorStatement.{uF, uW, uP, uE} :=
  let hTests := realOrdinaryPlaceTests_of_generation hGeneration realWhittakerRestrictionOnto
  relativeIsometryFactorStatement_of_realContinuation_and_tests hUnequal
    (fun F _ _ _ ψ hψ r t h _ => hTests.1 F ψ hψ r t h) hTests.2

end Langlands.Global.PoleComparison
