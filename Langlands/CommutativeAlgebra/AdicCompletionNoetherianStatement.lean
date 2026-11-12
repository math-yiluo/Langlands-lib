import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Noetherian.Basic

/-! # Noetherianity of adic completions: statement -/

universe u

namespace Langlands.CommutativeAlgebra

/-- The adic completion of a Noetherian commutative ring at any ideal is Noetherian
(Stacks Project, Algebra, Lemma 10.97.6, Tag 0316). The completion is Mathlib's
`AdicCompletion I R`. -/
def AdicCompletionNoetherianStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    IsNoetherianRing (AdicCompletion I R)

end Langlands.CommutativeAlgebra
