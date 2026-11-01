import Langlands.Representation.IntegerLattice.GeneralizedWeightBlock

/-! # One common strictly upper basis on each actual generalized-weight block -/

set_option autoImplicit false

namespace Langlands

universe u

open IntegerLattice

/-- One actual block basis simultaneously makes all normalized differences
strictly upper triangular and identifies the original generator matrices. -/
def CommutingTupleGeneralizedWeightBlockBasisStatement : Prop :=
  ∀ (d : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ),
    ∃ b : Module.Basis (Fin (Module.finrank ℂ (generalizedWeightBlock A c)))
        ℂ (generalizedWeightBlock A c),
      (∀ (t : Fin d) (i j : Fin (Module.finrank ℂ (generalizedWeightBlock A c))),
        j ≤ i → b.repr (normalizedGeneratorDifference A c t (b j)) i = 0) ∧
      (∀ t : Fin d,
        (generalizedWeightBlockGenerator A c t :
          Module.End ℂ (generalizedWeightBlock A c)) =
            (c t : ℂ) • (1 + normalizedGeneratorDifference A c t)) ∧
      (∀ (t : Fin d) (i j : Fin (Module.finrank ℂ (generalizedWeightBlock A c))),
        b.repr ((generalizedWeightBlockGenerator A c t :
          Module.End ℂ (generalizedWeightBlock A c)) (b j)) i =
            (c t : ℂ) * ((if i = j then 1 else 0) +
              b.repr (normalizedGeneratorDifference A c t (b j)) i)) ∧
      (∀ (t : Fin d) (i j : Fin (Module.finrank ℂ (generalizedWeightBlock A c))),
        j < i → b.repr ((generalizedWeightBlockGenerator A c t :
          Module.End ℂ (generalizedWeightBlock A c)) (b j)) i = 0) ∧
      (∀ (t : Fin d) (i : Fin (Module.finrank ℂ (generalizedWeightBlock A c))),
        b.repr ((generalizedWeightBlockGenerator A c t :
          Module.End ℂ (generalizedWeightBlock A c)) (b i)) i = (c t : ℂ))

end Langlands
