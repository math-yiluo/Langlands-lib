import Langlands.ClassField.Global.UnitTorsionSequence
import Langlands.ClassField.Global.ArchimedeanHerbrandFactor
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! # The cyclic Herbrand quotient of ordinary ring-integer units -/

namespace Langlands.ClassField.Global

universe u v

/-- For a cyclic Galois extension of number fields, the actual ordinary units have
finite first and second ordinary cohomology. Their Herbrand quotient, multiplied
by the extension degree, is the product of infinite-place stabilizer orders.
This states Milne VII, Proposition 3.1, specialized to all infinite places.
The declaration states the result; it does not prove it. -/
def CyclicUnitHerbrandQuotient : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (E : Type v) [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)],
    Finite (groupCohomology (ringIntegerUnitsRepresentation F E) 1 : Type v) ∧
      Finite (groupCohomology (ringIntegerUnitsRepresentation F E) 2 : Type v) ∧
      Module.finrank F E *
          Nat.card (groupCohomology (ringIntegerUnitsRepresentation F E) 2 : Type v) =
        archimedeanHerbrandFactor F E *
          Nat.card (groupCohomology (ringIntegerUnitsRepresentation F E) 1 : Type v)

end Langlands.ClassField.Global
