import Langlands.Representation.IntegerLattice.GeneralizedWeightBlock
import Mathlib.RingTheory.Binomial

/-! # All-integer products and finite binomial formulas on actual blocks -/

set_option autoImplicit false

namespace Langlands

universe u

open IntegerLattice

/-- Every actual restricted lattice action has the generator product, normalized
product and finite binomial product formulas, for all integer coordinates. -/
def CommutingTupleGeneralizedWeightProductStatement : Prop :=
  ∀ (d : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ) (n : Lattice d),
    (generalizedWeightBlockRepresentation A c n =
      (List.ofFn (fun i : Fin d =>
        ((generalizedWeightBlockGenerator A c i ^ n.toAdd i :
          (Module.End ℂ (generalizedWeightBlock A c))ˣ) :
            Module.End ℂ (generalizedWeightBlock A c)))).prod) ∧
    (generalizedWeightBlockRepresentation A c n =
      (coordinateCharacter c n : ℂ) •
        (List.ofFn (fun i : Fin d =>
          ((normalizedBlockGenerator A c i ^ n.toAdd i :
            (Module.End ℂ (generalizedWeightBlock A c))ˣ) :
              Module.End ℂ (generalizedWeightBlock A c)))).prod) ∧
    (generalizedWeightBlockRepresentation A c n =
      (coordinateCharacter c n : ℂ) •
        (List.ofFn (fun i : Fin d =>
          ∑ k ∈ Finset.range (Module.finrank ℂ V),
            Ring.choose (n.toAdd i : ℂ) k •
              normalizedGeneratorDifference A c i ^ k)).prod)

end Langlands
