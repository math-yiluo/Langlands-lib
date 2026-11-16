import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Finiteness.Defs

/-! # Statement: finite local algebras over Henselian local rings -/

universe u v

namespace Langlands.CommutativeAlgebra

/-- A finite algebra over a Henselian local ring is Henselian whenever its
underlying ring is local. This is Stacks Project, Tag 04GH, assertion (2). -/
def FiniteLocalHenselianStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [HenselianLocalRing R]
    (S : Type v) [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Finite R S],
      HenselianLocalRing S

end Langlands.CommutativeAlgebra
