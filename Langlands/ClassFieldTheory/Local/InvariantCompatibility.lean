import Langlands.ClassFieldTheory.Local.Invariants
import Langlands.ClassFieldTheory.Local.ClosureCoefficients

/-! # The actual finite-stage/absolute invariant compatibility diagram -/

namespace Langlands.ClassFieldTheory.Local.InvariantFamily

universe u

variable {p : ℕ} [Fact p.Prime]

/-- Compatibility of the relative and absolute invariant maps, tested on
actual continuous finite-stage classes through two constructed maps.
No ordinary-to-continuous comparison is supplied or presumed. -/
def ClosureCompatibility (I : InvariantFamily.{u,u} p) : Prop :=
  ∀ (F : PadicField.{u} p)
    (E : IntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    [FiniteDimensional F.Carrier E] [IsGalois F.Carrier E],
    ∀ x : continuousCohomology 2 (discreteUnitsRepresentation F.Carrier E),
      I.absolute F (closureContinuousInflation F.Carrier E 2 x) =
        I.relative F E (continuousToRelative F.Carrier E 2 x)

end Langlands.ClassFieldTheory.Local.InvariantFamily
