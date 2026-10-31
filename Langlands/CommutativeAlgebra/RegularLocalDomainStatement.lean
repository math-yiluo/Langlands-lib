import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Regular local rings are domains -/

universe u
namespace Langlands.CommutativeAlgebra

/-- Every regular local ring is a domain (Stacks Project, Lemma 10.106.2, Tag 00NP). -/
def RegularLocalDomainStatement : Prop :=
  ∀ (R : Type u) [CommRing R], IsRegularLocalRing R → IsDomain R

end Langlands.CommutativeAlgebra
