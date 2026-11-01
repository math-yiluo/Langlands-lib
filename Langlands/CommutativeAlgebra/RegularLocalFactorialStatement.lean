import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-! # Regular local rings are unique factorization domains -/

universe u

namespace Langlands.CommutativeAlgebra

/-- Every regular local ring is a UFD (Stacks Project, Lemma 15.123.2, Tag 0AG0).
This definition states the assertion without proving it. -/
def RegularLocalFactorialStatement : Prop :=
  ∀ (R : Type u) [CommRing R],
    IsRegularLocalRing R → UniqueFactorizationMonoid R

end Langlands.CommutativeAlgebra
