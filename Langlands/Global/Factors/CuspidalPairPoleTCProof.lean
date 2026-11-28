import Langlands.Global.Factors.CuspidalPairPartialGammaGlobalTCReduction
import Langlands.Global.Factors.CuspidalPairPartialGammaTCReduction
import Langlands.Global.Factors.CuspidalPairPoleComplexRestrictionProof
import Langlands.Global.Factors.CuspidalPairPoleTCRemainingInputs
import Langlands.Global.RankinSelberg.ComplexOrdinaryNormalizedGenerationProof
import Langlands.Global.RankinSelberg.ComplexUnequalOrdinaryPlaceTestsProof
import Langlands.Global.RankinSelberg.EqualAnalyticProof
import Langlands.Global.RankinSelberg.EqualDualEulerFactorizationProof
import Langlands.Global.RankinSelberg.EqualEulerFactorizationProof
import Langlands.Global.RankinSelberg.EqualSemilocalEquationTCFromOrdinaryTests
import Langlands.Global.RankinSelberg.EqualUnfoldingProof
import Langlands.Global.RankinSelberg.UnequalAnalyticProof
import Langlands.Global.RankinSelberg.UnequalDualEulerFactorizationProof
import Langlands.Global.RankinSelberg.UnequalEulerFactorizationProof
import Langlands.Global.RankinSelberg.UnequalFactorizationAtReductionProof
import Langlands.Global.RankinSelberg.UnequalInfiniteWhittakerSliceReduction
import Langlands.Global.RankinSelberg.UnequalSemilocalArchimedeanReduction
import Langlands.Global.RankinSelberg.UnequalUnfoldingProof

/-! # Poles and vertical-strip bounds of completed cuspidal pair L-functions over totally complex fields -/

set_option autoImplicit false

universe u uQ

namespace Langlands.Global.CuspidalPairPoles

open NumberField RankinSelbergGlobal HeckeFunctionalEquation

private theorem noRealPlace {F : Type u} [Field F] [NumberField F] [IsTotallyComplex F]
    (v : {v : InfinitePlace F // v.IsReal}) : False :=
  InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v.1) v.2

set_option maxHeartbeats 1000000 in
private theorem unequalPointwiseFactorizationAt_of_isTotallyComplex
    (F : Type u) [Field F] [NumberField F] [IsTotallyComplex F] [CompactSpace (AdeleQuotient F)] :
    UnequalPointwiseFactorizationAt.{u, uQ} F := by
  apply unequalPointwiseOfInfiniteTestsAt F
  intro ψ hψ r t h T Td T' Td' hTd hTd' P P' hI hI' S hPS hPS' hsupp aR _ aC haC
    dR dR' _ _ hdR hdR' _ _ dC dC' dCd dCd' hdC hdC' hdCd hdCd'
    ψv hψv ℓ ℓ' a₀ a₀' ha₀ ha₀'
  have hχ := UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ hψ
  let ψ' := inverseCharacter ψ
  have hχ' := UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ'
    (inverseCharacter_rational ψ hψ)
  obtain ⟨M⟩ := infiniteWhittakerSliceModelAt_of_isTotallyComplex F r T P hI ψ.complex hχ dR hdR dC hdC
  obtain ⟨M'⟩ := infiniteWhittakerSliceModelAt_of_isTotallyComplex F t T' P' hI' ψ'.complex hχ'
    dR' hdR' dC' hdC'
  have hTest := complexUnequalPlaceTests_of_ordinary
    complexPlaceFunctionalEquation.1 complexUnequalOrdinaryPlaceTests
  exact unequalInfiniteWhittakerTest_of_placeData ψ hψ h P P' hI hI' S hPS hPS' hsupp
    aR aC ψv hψv ℓ ℓ' a₀ a₀' ha₀ ha₀' M
    (by simpa only [ψ', complex_inverseCharacter] using M')
    (fun v => (noRealPlace v).elim)
    (fun w => hTest F ψ hψ r t h T Td T' Td' hTd hTd' w (aC w) (haC w)
      (dC w) (dC' w) (dCd w) (dCd' w) (hdC w) (hdC' w) (hdCd w) (hdCd' w))

private theorem unequalSemilocalEquationTC : UnequalSemilocalEquationTCStatement.{u, uQ} := by
  apply unequalSemilocalEquationTC_of_factorizationTC
  intro F _ _ _ _
  exact UnequalSemilocalArchimedeanReduction.factorization_of_at complexPlaceFunctionalEquation.1
    archimedeanCentralSign F
    (unequalArchimedeanFactorizationAtReduction F (unequalPointwiseFactorizationAt_of_isTotallyComplex F))
    (fun v => (noRealPlace v).elim)

/-- The pole profile and vertical-strip bounds of completed cuspidal pair L-functions
over totally complex number fields, with existence of the local data. -/
theorem cuspidalPairPoleTC : CuspidalPairPoleTCStatement.{u, uQ} := by
  apply cuspidalPairPoleTCRemainingInputs _
    complexOrdinaryNormalizedGeneration
    (fun F _ _ _ _ => infiniteWhittakerSliceModelAt_of_isTotallyComplex F)
    complexPlaceWhittakerRestrictionSurjectivity
  exact cuspidalPairPartialGammaTCReduction
    (cuspidalPairPartialGammaGlobalTCReduction UnequalAnalytic.unequalAnalyticStatement_proof
      unequalUnfoldingStatement_proof unequalEulerFactorization unequalDualEulerFactorization
      unequalSemilocalEquationTC
      EqualAnalytic.equalAnalyticStatement_proof equalUnfoldingStatement_proof
      equalEulerFactorization equalDualEulerFactorization
      (equalSemilocalEquationTC_of_ordinaryGeneration complexOrdinaryNormalizedGeneration))

end Langlands.Global.CuspidalPairPoles
