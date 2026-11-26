import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityStatement
import Langlands.Automorphic.Unramified.CyclicPrimeJointRankInductionStatement

/-! # Reduction of prime cyclic isobaric weak base change over arbitrary number fields -/

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global

/-- Recover the upper datum of a supplied weak base change from Euler constituent recovery
over the upper field. The extension and the isobaric data can be arbitrary. -/
def IsobaricWeakBaseChangeUniquenessStatement : Prop :=
  CuspidalEulerConstituentRecoveryStatement.{uE, uW} →
    ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
      [Algebra F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
      (DF : IsobaricData F) (DE DE' : IsobaricData E),
      IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW} DE DF →
      IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW} DE' DF → DE = DE'

/-- Going up at every positive rank and Euler constituent recovery imply Arthur–Clozel
III.4.2(c) over arbitrary number fields. -/
def CyclicPrimeIsobaricBaseChangeReductionStatement : Prop :=
  CyclicPrimeJointRankInductionStatement.{uF, uE, uV, uW} →
  CuspidalEulerConstituentRecoveryStatement.{uE, uW} →
    CyclicPrimeIsobaricBaseChangeStatement.{uF, uE, uV, uW}

end Langlands.Automorphic.Unramified
