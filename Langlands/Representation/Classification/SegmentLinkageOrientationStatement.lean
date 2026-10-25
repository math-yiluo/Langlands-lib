import Langlands.Representation.Classification.Segments

/-!
# Orientation of linked segments

This internal statement isolates the finite support argument that two linked
segments have a precedence relation in at least one direction.
-/

namespace Langlands.Classification

universe uF uV

/-- Linked segments precede one another in at least one direction. -/
def SegmentLinkageOrientation
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  ∀ (Δ Γ : T.Segment.{uV,uF}), Δ.IsLinked Γ → Δ.Precedes Γ ∨ Γ.Precedes Δ

end Langlands.Classification
