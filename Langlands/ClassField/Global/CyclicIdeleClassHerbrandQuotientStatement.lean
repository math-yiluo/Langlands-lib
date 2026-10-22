import Langlands.ClassField.Global.Cohomology
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! # The cyclic Herbrand quotient of the actual idele class group -/

namespace Langlands.ClassField.Global

universe u v

/-- The first fundamental inequality in its Herbrand-quotient form: for a cyclic
extension of number fields, the actual first and second idele-class cohomology
groups are finite and their orders satisfy `h²(C_E) = [E : F] * h¹(C_E)`.
This declaration states Artin–Tate, Chapter V, Theorem 1; it does not prove it. -/
def CyclicIdeleClassHerbrandQuotient : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (E : Type v) [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)],
    Finite (relativeIdeleClassCohomology F E 1 : Type v) ∧
      Finite (relativeIdeleClassCohomology F E 2 : Type v) ∧
      Nat.card (relativeIdeleClassCohomology F E 2 : Type v) =
        Module.finrank F E * Nat.card (relativeIdeleClassCohomology F E 1 : Type v)

end Langlands.ClassField.Global
