import Langlands.Automorphic.Unramified.CyclicPrimeCuspidalBaseChangeExistenceTCStatement
import Langlands.Automorphic.Unramified.CyclicPrimeJointRankInductionStatement
import Langlands.Automorphic.Unramified.CyclicPrimeSingletonBaseChange
import Langlands.Automorphic.CuspidalUnitaryForm

/-! # Singleton weak base change from the totally complex joint rank induction -/

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Automorphic.CuspidalOperatorRealization

/-- Joint rank induction over a totally complex base implies the existence of
unitary weak base change for a unitary cuspidal singleton. -/
def CyclicPrimeCuspidalBaseChangeExistenceTCReductionStatement : Prop :=
  CyclicPrimeJointRankInductionTCStatement.{uF, uE, uV, uW} →
  CyclicPrimeCuspidalBaseChangeExistenceTCStatement.{uF, uE, uV, uW}

/-- The going-up clauses of the joint rank induction give unitary weak base change
for each unitary cuspidal singleton over a totally complex base. -/
theorem cyclicPrimeCuspidalBaseChangeExistenceTC_of_jointRankInduction :
    CyclicPrimeCuspidalBaseChangeExistenceTCReductionStatement.{uF, uE, uV, uW} := by
  intro hInduction F E _ _ _ _ _ _ _ _ _ hprime c hc
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

end Langlands.Automorphic.Unramified
