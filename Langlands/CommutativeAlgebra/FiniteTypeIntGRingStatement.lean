import Langlands.CommutativeAlgebra.RegularRingMaps
import Mathlib.RingTheory.FiniteType

/-! # Finite-type integer algebras are G-rings: statement -/

universe u

namespace Langlands.CommutativeAlgebra

/-- Every commutative finite-type integer algebra is a G-ring. -/
def FiniteTypeIntGRingStatement : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra.FiniteType ℤ S], IsGRing S

end Langlands.CommutativeAlgebra
