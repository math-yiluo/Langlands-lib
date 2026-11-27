import Langlands.Global.Factors.CuspidalPairPoleGapGrowthReduction
import Langlands.Global.Factors.CuspidalPairPoleRealRestrictionProof
import Langlands.Global.Factors.CuspidalPairPoleComplexRestrictionProof
import Langlands.Global.RankinSelberg.InfiniteWhittakerSliceProof
import Langlands.Global.RankinSelberg.RealWhittakerModelUniformityProof
import Langlands.Global.RankinSelberg.ComplexOrdinaryNormalizedGenerationProof
import Langlands.Global.RankinSelberg.RealLocalUniformUnequalContinuationProof
import Langlands.Global.RankinSelberg.RealLocalUniformPositiveEqualContinuationProof
import Langlands.Global.RankinSelberg.RealUniformContinuationReduction
import Langlands.Global.RankinSelberg.RealPlaceContragredientReduction
import Langlands.Global.RankinSelberg.RealStandardPairingReduction
import Langlands.Global.RankinSelberg.RealStandardDualPairingProof
import Langlands.Global.RankinSelberg.RealStandardIntertwinerPairLProof
import Langlands.Automorphic.CuspidalArchimedeanComponentIrreducibleProof
import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationLocalFEReduction
import Langlands.Global.RankinSelberg.ComplexPlaceUnequalFunctionalEquationProof
import Langlands.Global.RankinSelberg.ComplexPlaceEqualFunctionalEquationProof
import Langlands.Global.RankinSelberg.ArchimedeanCentralSignProof
import Langlands.Global.RankinSelberg.UnequalSemilocalArchimedeanReduction
import Langlands.Global.RankinSelberg.EqualSemilocalFactorizationReduction
import Langlands.Global.RankinSelberg.EqualSemilocalReduction
import Langlands.Global.RankinSelberg.UnequalAnalyticProof
import Langlands.Global.RankinSelberg.UnequalUnfoldingProof
import Langlands.Global.RankinSelberg.UnequalEulerFactorizationProof
import Langlands.Global.RankinSelberg.UnequalDualEulerFactorizationProof
import Langlands.Global.RankinSelberg.EqualAnalyticProof
import Langlands.Global.RankinSelberg.EqualUnfoldingProof
import Langlands.Global.RankinSelberg.EqualEulerFactorizationProof
import Langlands.Global.RankinSelberg.EqualDualEulerFactorizationProof
import Langlands.Global.Factors.CuspidalPairPartialGammaGlobalReduction
import Langlands.Global.Factors.CuspidalPairPartialGammaReduction
import Langlands.Global.Factors.CuspidalPairFunctionalEquationReduction
import Langlands.Global.Factors.CuspidalPairLocalDataProof
import Langlands.Global.Factors.CuspidalArchimedeanParameterExistenceProof
import Langlands.Global.Factors.CuspidalSatakeBoundReduction
import Langlands.Automorphic.IrreducibleCentralCharacterProof

/-! # The cuspidal pair functional equation and pole theorem from the archimedean factorization

The completed global Rankin–Selberg functional equation of cuspidal pairs follows from the
archimedean factorization `RankinSelbergGlobal.ArchimedeanFactorizationStatement` and proved
Library theorems. With the real ordinary continuation and generation statements, it gives the
cuspidal pair pole proposition. See the paired Markdown.
-/

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal

/-- **The archimedean Rankin–Selberg functional equation at the real places, both ranks**
(Jacquet 2009, Theorem 2.1): the uniform continuation reduction applied to the uniform
unequal-rank and positive equal-rank continuations and to the contragredient pair-factor
identity. -/
theorem realPlaceFunctionalEquation_of_uniformContinuation :
    RealPlaceFunctionalEquationStatement.{u} :=
  realPlaceUniformContinuationReduction realLocalUniformUnequalContinuation
    realLocalUniformPositiveEqualContinuation
    (realPlaceContragredientPairLReduction Automorphic.cuspidalArchimedeanStandardIrreducible
      (realStandardPairingPairLReduction realStandardDualPairing realStandardIntertwinerPairL))

/-- The archimedean semi-local theory from the archimedean factorization: the functional
equations at the complex and real places and the central sign are proved. -/
theorem archimedeanSemilocalTheory_of_factorization
    (hFac : ArchimedeanFactorizationStatement.{u, uQ}) :
    ArchimedeanSemilocalTheoryStatement.{u, uQ} :=
  ⟨⟨complexPlaceFunctionalEquationLocalFEReduction complexLocalUnequalFunctionalEquation
      complexLocalEqualFunctionalEquation, realPlaceFunctionalEquation_of_uniformContinuation⟩,
    hFac, archimedeanCentralSign⟩

end Langlands.Global.RankinSelbergGlobal

namespace Langlands.Global

open RankinSelbergGlobal

/-- **Conditional global functional equation** (Cogdell 2004, proof of Theorem 4.1): the
archimedean factorization over `S` and the infinite places implies the completed global
Rankin–Selberg functional equation of actual cuspidal pairs in both universes. -/
def CuspidalPairFunctionalEquationFactorizationStatement : Prop :=
  ArchimedeanFactorizationStatement.{u, uQ} →
    CuspidalPairGlobalFunctionalEquationStatement.{u, uQ}

/-- Proof of `CuspidalPairFunctionalEquationFactorizationStatement`: the semi-local equations
in both ranks, the partial equation with integral gamma factors, the completed equation and the
global equation, by the Library's reductions and proved premises. -/
theorem cuspidalPairFunctionalEquationFactorization :
    CuspidalPairFunctionalEquationFactorizationStatement.{u, uQ} := by
  intro hFac
  have hA := archimedeanSemilocalTheory_of_factorization hFac
  have hU : UnequalSemilocalEquationStatement.{u, uQ} := unequalSemilocalArchimedeanReduction hA
  have hE : EqualSemilocalEquationStatement.{u, uQ} :=
    equalSemilocalReduction (equalSemilocalFactorization_of_archimedeanSemilocalTheory hA)
  have hG : CuspidalPairPartialGammaEquationStatement.{u, uQ} :=
    cuspidalPairPartialGammaGlobalReduction UnequalAnalytic.unequalAnalyticStatement_proof
      unequalUnfoldingStatement_proof unequalEulerFactorization unequalDualEulerFactorization hU
      EqualAnalytic.equalAnalyticStatement_proof equalUnfoldingStatement_proof
      equalEulerFactorization equalDualEulerFactorization hE
  exact cuspidalPairFunctionalEquationReduction cuspidalPairLocalData
    cuspidalArchimedeanParameterExistence
    (cuspidalPairCompletedEquation_of_satakeBound_of_partialGamma
      (cuspidalSatakeBoundReduction Automorphic.OperatorRealization.irreducibleCentralCharacter) hG)

end Langlands.Global

namespace Langlands.Global.CuspidalPairPoles

open RankinSelbergGlobal

/-- The archimedean factorization, the real ordinary continuation and the real ordinary
generation imply the cuspidal pair pole proposition in both universes. -/
def CuspidalPairPoleFactorizationInputsStatement : Prop :=
  ArchimedeanFactorizationStatement.{u, uQ} →
    RealOrdinaryNormalizedContinuationStatement → RealOrdinaryNormalizedGenerationStatement →
    CuspidalPairPoleStatement.{u, uQ}

theorem cuspidalPairPoleFactorizationInputs :
    CuspidalPairPoleFactorizationInputsStatement.{u, uQ} := by
  intro hFac hRC hRG
  exact cuspidalPairPoleGapGrowthInputs (cuspidalPairFunctionalEquationFactorization hFac) hRC hRG
    complexOrdinaryNormalizedGeneration infiniteWhittakerSliceModel
    realPlaceWhittakerRestrictionSurjectivity complexPlaceWhittakerRestrictionSurjectivity
    realWhittakerModelUniformity RealJacquet.realLocalUnequalCharacterGrowth_gap

end Langlands.Global.CuspidalPairPoles
