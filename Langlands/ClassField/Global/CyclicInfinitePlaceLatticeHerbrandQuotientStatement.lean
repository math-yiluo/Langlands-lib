import Langlands.ClassField.Global.InfinitePlaceLattice
import Langlands.ClassField.Global.ArchimedeanHerbrandFactor
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! # The cyclic Herbrand quotient of the infinite-place permutation lattice -/

namespace Langlands.ClassField.Global

universe u v

/-- For a cyclic Galois extension of number fields, the infinite-place integer
permutation lattice has finite first and second ordinary cohomology, with
Herbrand quotient equal to the product of infinite-place stabilizer orders.
This is the permutation-lattice calculation in Milne VII, proof of Proposition 3.1.
The declaration states the result; it does not prove it. -/
def CyclicInfinitePlaceLatticeHerbrandQuotient : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (E : Type v) [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)],
    Finite (infinitePlaceLatticeCohomology F E 1 : Type v) ∧
      Finite (infinitePlaceLatticeCohomology F E 2 : Type v) ∧
      Nat.card (infinitePlaceLatticeCohomology F E 2 : Type v) =
        archimedeanHerbrandFactor F E *
          Nat.card (infinitePlaceLatticeCohomology F E 1 : Type v)

end Langlands.ClassField.Global
