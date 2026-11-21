import Langlands.Automorphic.Unramified.CyclicPrimeIsobaricBaseChangeTCStatement
import Langlands.Automorphic.Unramified.CyclicPrimeSingletonBaseChange
import Langlands.Automorphic.Unramified.IsobaricWeakBaseChangeSum
import Langlands.Automorphic.Unramified.IsobaricWeakBaseChangeUniqueness

/-! # Assembly of prime cyclic isobaric base change over a totally complex base -/

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global IsobaricData

/-- Unitary singleton lifts over totally complex bases and Euler constituent recovery
give existence and uniqueness of isobaric weak base change. -/
def CyclicPrimeIsobaricBaseChangeTCAssemblyStatement : Prop :=
  (∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F]
      [NumberField.IsTotallyComplex F] [Field E] [NumberField E]
      [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
      [CompactSpace (AdeleQuotient E)],
      (Module.finrank F E).Prime →
      ∀ c : PositiveRankCuspidalClass F, (ofCuspidal c).IsUnitary →
        ∃ DE : IsobaricData E, DE.IsUnitary ∧
          IsWeakBaseChangeOf.{uF, uE, uV, uW} DE (ofCuspidal c)) →
  CuspidalEulerConstituentRecoveryTCStatement.{uE, uW} →
  CyclicPrimeIsobaricBaseChangeTCStatement.{uF, uE, uV, uW}

theorem cyclicPrimeIsobaricBaseChangeTC_of_singletons :
    CyclicPrimeIsobaricBaseChangeTCAssemblyStatement.{uF, uE, uV, uW} := by
  intro lift recovery F E _ _ _ _ _ _ _ _ _ hPrime DF hDF
  let _ : NumberField.IsTotallyComplex E := NumberField.isTotallyComplex_of_algebra F E
  obtain ⟨DE, hDE, hBaseChange⟩ :=
    exists_unitary_weakBaseChange_of_singletons (F := F) (E := E) (lift F E hPrime) DF hDF
  exact ⟨DE, hDE, hBaseChange, fun _ _ h =>
    IsWeakBaseChangeOf.unique_of_eulerConstituentRecoveryTC recovery h hBaseChange⟩

/-- The two published prime cyclic lift propositions imply the singleton input. -/
theorem cyclicPrimeIsobaricBaseChangeTC_of_cuspidal
    (hLift : CyclicPrimeIsobaricLiftStatement.{uF, uE, uV, uW})
    (hSelfTwist : CyclicPrimeIsobaricSelfTwistStatement.{uF, uE, uV, uW})
    (recovery : CuspidalEulerConstituentRecoveryTCStatement.{uE, uW}) :
    CyclicPrimeIsobaricBaseChangeTCStatement.{uF, uE, uV, uW} := by
  apply cyclicPrimeIsobaricBaseChangeTC_of_singletons _ recovery
  intro F E _ _ _ _ _ _ _ _ _ hPrime c hc
  exact cyclicPrimeSingletonBaseChange_of_cuspidal (F := F) (E := E) hLift hSelfTwist hPrime c hc

end Langlands.Automorphic.Unramified
