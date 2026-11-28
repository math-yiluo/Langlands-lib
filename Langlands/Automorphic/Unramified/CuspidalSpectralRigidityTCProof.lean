import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityTCPoleProfileReduction
import Langlands.Global.Factors.CuspidalPairPoleComplexRestrictionProof
import Langlands.Global.Factors.CuspidalPairPoleTCRemainingInputs
import Langlands.Global.RankinSelberg.ComplexOrdinaryNormalizedGenerationProof
import Langlands.Global.RankinSelberg.EqualSemilocalEquationTCFromOrdinaryTests

/-! # Cuspidal spectral rigidity over totally complex number fields -/

set_option autoImplicit false

universe uF uV

namespace Langlands.Automorphic.Unramified

open Langlands.Global CuspidalPairPoles RankinSelbergGlobal

/-- Independence and constituent recovery for supplied cuspidal spectral systems
over totally complex number fields. -/
theorem cuspidalSpectralRigidityTC : CuspidalSpectralRigidityTCStatement.{uF, uV} := by
  apply cuspidalSpectralRigidityTC_of_normalizedContinuation
  intro F _ _ _ _
  exact cuspidalPairNormalizedContinuationTCAt_of_local F
    complexOrdinaryNormalizedAllGrowth.1 complexOrdinaryNormalizedGeneration
    complexOrdinaryNormalizedAllGrowth.2
    (specifiedWhittakerSliceComparisonAt_of_complex F
      (infiniteWhittakerSliceModelAt_of_isTotallyComplex F)
      complexPlaceWhittakerRestrictionSurjectivity)

end Langlands.Automorphic.Unramified
