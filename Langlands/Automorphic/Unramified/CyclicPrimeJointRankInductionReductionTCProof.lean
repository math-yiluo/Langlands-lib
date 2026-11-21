import Langlands.Automorphic.Unramified.CyclicPrimeJointRankInductionStatement

/-! # Strong induction over a totally complex base -/

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

/-- The totally complex analytic rank steps give joint existence at every
positive total rank over a totally complex base. -/
theorem cyclicPrimeJointRankInductionReductionTC :
    CyclicPrimeJointRankInductionReductionTCStatement.{uF, uE, uV, uW} := by
  intro hStep F E _ _ instTotallyComplex _ _ _ _ _ _ hPrime σ hGenerator η hNorm n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    obtain ⟨goingUp, goingDown⟩ := hStep F E hPrime σ hGenerator η hNorm n hn
    exact ⟨goingUp (fun k hk hkn ↦ (ih k hkn hk).2),
      goingDown (fun k hk hkn ↦ (ih k hkn hk).1)⟩

end Langlands.Automorphic.Unramified
