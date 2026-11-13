import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Regular.RegularSequence

/-! # A regular system of parameters mapping to a regular sequence gives flatness -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Lemma 10.128.2 (07DY): let `R → S` be a local homomorphism of Noetherian
local rings and `x` a regular sequence of `R` generating the maximal ideal (that is, a
regular system of parameters of the regular local ring `R`). If the image of `x` is a
regular sequence of `S`, then `S` is flat over `R`. -/
def RegularSequenceFlatStatement : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsNoetherianRing R]
    [IsLocalRing S] [IsNoetherianRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    (x : List R),
    Ideal.ofList x = IsLocalRing.maximalIdeal R →
    RingTheory.Sequence.IsWeaklyRegular R x →
    RingTheory.Sequence.IsWeaklyRegular S (x.map (algebraMap R S)) →
      Module.Flat R S

end Langlands.CommutativeAlgebra.Popescu
