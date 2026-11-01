import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Prime localizations of regular local rings are regular -/

universe u

namespace Langlands.CommutativeAlgebra

/-- Every regular local ring is a regular ring: each of its localizations at a prime ideal is a
regular local ring (Stacks Project, Lemma 10.110.6, Tag 0AFS, second sentence). This definition
states the assertion without proving it. -/
def RegularLocalLocalizationsStatement : Prop :=
  ∀ (R : Type u) [CommRing R], IsRegularLocalRing R → IsRegularRing R

end Langlands.CommutativeAlgebra
