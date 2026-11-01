import Langlands.Representation.IntegerLattice.GeneralizedWeightBlock

/-! # One global block basis for every actual integer-lattice action -/

set_option autoImplicit false

namespace Langlands

universe u

open IntegerLattice

/-- A single ambient basis assembled from the actual generalized-weight blocks
makes every integer-lattice action block diagonal with upper triangular blocks
whose diagonals are the corresponding coordinate characters. -/
def CommutingTupleGeneralizedWeightGlobalBasisStatement : Prop :=
  ∀ (d : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : CommutingInvertibleTuple d V),
    ∃ (b : ∀ c : Fin d → ℂˣ,
        Module.Basis (Fin (Module.finrank ℂ (generalizedWeightBlock A c)))
          ℂ (generalizedWeightBlock A c))
      (B : Module.Basis
        (Σ c : Fin d → ℂˣ, Fin (Module.finrank ℂ (generalizedWeightBlock A c))) ℂ V),
      (∀ (c : Fin d → ℂˣ) (j : Fin (Module.finrank ℂ (generalizedWeightBlock A c))),
        B ⟨c, j⟩ = (b c j : V)) ∧
      (∀ (c : Fin d → ℂˣ) (t : Fin d)
        (i j : Fin (Module.finrank ℂ (generalizedWeightBlock A c))),
        j ≤ i → (b c).repr (normalizedGeneratorDifference A c t (b c j)) i = 0) ∧
      (∀ (n : Lattice d) (c c' : Fin d → ℂˣ)
        (i : Fin (Module.finrank ℂ (generalizedWeightBlock A c)))
        (j : Fin (Module.finrank ℂ (generalizedWeightBlock A c'))),
        c ≠ c' →
          B.repr (tupleRepresentationEquiv d V A n (B ⟨c', j⟩)) ⟨c, i⟩ = 0) ∧
      (∀ (n : Lattice d) (c : Fin d → ℂˣ)
        (i j : Fin (Module.finrank ℂ (generalizedWeightBlock A c))),
        j < i → B.repr (tupleRepresentationEquiv d V A n (B ⟨c, j⟩)) ⟨c, i⟩ = 0) ∧
      (∀ (n : Lattice d) (c : Fin d → ℂˣ)
        (i : Fin (Module.finrank ℂ (generalizedWeightBlock A c))),
        B.repr (tupleRepresentationEquiv d V A n (B ⟨c, i⟩)) ⟨c, i⟩ =
          (coordinateCharacter c n : ℂ))

end Langlands
