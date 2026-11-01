import Langlands.Representation.IntegerLattice
import Langlands.Representation.IntegerLattice.GeneralizedWeightBlock

/-! # Common eigenvectors and the finite list of occurring lattice characters -/

set_option autoImplicit false

namespace Langlands

universe u

open IntegerLattice

/-- Unit labels are recovered at the generators, and every lattice character
is reconstructed from its values there. -/
def IntegerLatticeCoordinateCharacterReconstructionStatement : Prop :=
  ∀ d : ℕ,
    (∀ χ : Lattice d →* ℂˣ,
      coordinateCharacter (fun i => χ (generator d i)) = χ) ∧
    Function.Injective (coordinateCharacter (d := d))

/-- The same vector is a common eigenvector for the generators exactly when
every lattice point acts on it by the associated coordinate character. -/
def CommutingTupleCommonEigenvectorCharacterStatement : Prop :=
  ∀ (d : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ) (v : V),
    (∀ i : Fin d, (A.1 i : Module.End ℂ V) v = (c i : ℂ) • v) ↔
      ∀ n : Lattice d,
        tupleRepresentationEquiv d V A n v = (coordinateCharacter c n : ℂ) • v

/-- One finite list of labels enumerates exactly the nonzero actual blocks
and exactly all characters realized on nonzero common eigenvectors. -/
def CommutingTupleOccurringCharacterEnumerationStatement : Prop :=
  ∀ (d : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : CommutingInvertibleTuple d V),
    ∃ (l : ℕ) (c : Fin l → Fin d → ℂˣ),
      Function.Injective (fun j => coordinateCharacter (c j)) ∧
      (∀ b : Fin d → ℂˣ,
        generalizedWeightBlock A b ≠ ⊥ ↔ ∃ j : Fin l, c j = b) ∧
      ∀ χ : Lattice d →* ℂˣ,
        (∃ v : V, v ≠ 0 ∧
          ∀ n : Lattice d, tupleRepresentationEquiv d V A n v = (χ n : ℂ) • v) ↔
        ∃ j : Fin l, coordinateCharacter (c j) = χ

/-- Source comparisons for Renard C.III's finite list of distinct characters. -/
def RenardCIIIOccurringCharactersStatement : Prop :=
  IntegerLatticeCoordinateCharacterReconstructionStatement ∧
    CommutingTupleCommonEigenvectorCharacterStatement.{u} ∧
    CommutingTupleOccurringCharacterEnumerationStatement.{u}

end Langlands
