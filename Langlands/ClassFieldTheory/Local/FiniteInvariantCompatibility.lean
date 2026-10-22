import Langlands.ClassFieldTheory.Local.InvariantCompatibility
import Langlands.ClassFieldTheory.Local.FiniteComparison

/-! # The invariant diagram on ordinary relative classes -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u

namespace InvariantFamily

/-- Compatibility of relative and absolute invariants on every ordinary relative
class, using the constructed ordinary-to-absolute inflation map. -/
def OrdinaryClosureCompatibility {p : ℕ} [Fact p.Prime]
    (I : InvariantFamily.{u,u} p) : Prop :=
  ∀ (F : PadicField.{u} p)
    (E : IntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    [FiniteDimensional F.Carrier E] [IsGalois F.Carrier E],
    ∀ x : relativeCohomology F.Carrier E 2,
      I.absolute F (closureInflation F.Carrier E 2 x) = I.relative F E x

/-- The compatibility predicate on continuous representatives is equivalent to
the full diagram on ordinary relative classes, by the proved finite comparison. -/
theorem closureCompatibility_iff {p : ℕ} [Fact p.Prime]
    (I : InvariantFamily.{u,u} p) :
    ClosureCompatibility I ↔ OrdinaryClosureCompatibility I := by
  constructor
  · intro h F E _ _ x
    have hx := h F E ((continuousToRelativeEquiv F.Carrier E 2).symm x)
    change I.absolute F (closureInflation F.Carrier E 2 x) =
      I.relative F E
        (continuousToRelativeEquiv F.Carrier E 2
          ((continuousToRelativeEquiv F.Carrier E 2).symm x)) at hx
    simpa only [AddEquiv.apply_symm_apply] using hx
  · intro h F E _ _ x
    have hx := h F E (continuousToRelative F.Carrier E 2 x)
    rw [closureInflation_continuousToRelative] at hx
    exact hx

end InvariantFamily

end Langlands.ClassFieldTheory.Local
