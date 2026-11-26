import Langlands.Automorphic.Unramified.IsobaricWeakBaseChangeUniquenessProof
import Langlands.Automorphic.Unramified.IsobaricWeakBaseChangeSum
import Langlands.Automorphic.Unramified.CyclicPrimeSingletonBaseChange
import Langlands.Automorphic.CuspidalUnitaryForm

/-! # Prime cyclic isobaric weak base change from the joint rank induction -/

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Automorphic.CuspidalOperatorRealization

/-- The going-up clauses of the joint rank induction give a unitary weak base change of
the singleton datum of each unitary cuspidal class, along a Galois extension of prime
degree of arbitrary number fields. -/
theorem exists_unitary_weakBaseChange_ofCuspidal_of_jointRankInduction
    (hInduction : CyclicPrimeJointRankInductionStatement.{uF, uE, uV, uW})
    {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)] (hprime : (Module.finrank F E).Prime)
    (c : PositiveRankCuspidalClass F) (hc : (IsobaricData.ofCuspidal c).IsUnitary) :
    ∃ DE : IsobaricData E, DE.IsUnitary ∧
      IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW} DE (IsobaricData.ofCuspidal c) := by
  classical
  let _ : Fact (Module.finrank F E).Prime := ⟨hprime⟩
  let _ : IsCyclic (E ≃ₐ[F] E) :=
    isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank F E)
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := E ≃ₐ[F] E)
  obtain ⟨η, hη⟩ := (HeckeCharacter.cyclicNormKernelCharacter.{uF, uE} F E).1
  rcases c with ⟨r, c⟩
  obtain ⟨S, rfl⟩ := c.exists_representative
  have hUnitary : S.realization.IsUnitarizable := IsobaricData.isUnitary_ofCuspidal.mp hc
  have hCentral := S.hasUnitaryCentralCharacter_of_isUnitarizable hUnitary
  have hGoingUp := (hInduction F E hprime σ hσ η hη (r + 1) (Nat.succ_pos r)).1
    r S rfl hCentral
  by_cases hTwist : IsoClass.IsFiniteOrderDeterminantTwist η S.isoClass S.isoClass
  · obtain ⟨m, T, _, _, _, hOrbitUnitary, hBaseChange⟩ := hGoingUp.2 hTwist
    exact ⟨IsobaricData.galoisOrbit F (PositiveRankCuspidalClass.ofFixedRank T.isoClass),
      hOrbitUnitary, hBaseChange⟩
  · obtain ⟨T, hUpperCentral, _, hBaseChange⟩ := hGoingUp.1 hTwist
    exact ⟨IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank T.isoClass),
      IsobaricData.isUnitary_ofCuspidal.mpr
        (T.isUnitarizable_of_hasUnitaryCentralCharacter hUpperCentral),
      (IsobaricData.isWeakBaseChangeOf_ofCuspidal_iff.{uF, uE, uV, uW}
        T.isoClass S.isoClass).mpr hBaseChange⟩

/-- The joint rank induction and upper Euler constituent recovery give existence and
uniqueness of unitary isobaric weak base change along Galois extensions of prime degree
of arbitrary number fields. -/
theorem cyclicPrimeIsobaricBaseChangeReduction :
    CyclicPrimeIsobaricBaseChangeReductionStatement.{uF, uE, uV, uW} := by
  intro hInduction hRecovery F E _ _ _ _ _ _ _ _ hPrime DF hDF
  obtain ⟨DE, hDE, hBaseChange⟩ :=
    IsobaricData.exists_unitary_weakBaseChange_of_singletons (F := F) (E := E)
      (exists_unitary_weakBaseChange_ofCuspidal_of_jointRankInduction hInduction hPrime) DF hDF
  exact ⟨DE, hDE, hBaseChange, fun _ _ h =>
    IsobaricData.IsWeakBaseChangeOf.unique_of_eulerConstituentRecovery hRecovery h hBaseChange⟩

end Langlands.Automorphic.Unramified
