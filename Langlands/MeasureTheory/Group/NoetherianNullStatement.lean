import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.NoetherianSpace

/-! # Null inverse images of proper Noetherian closed sets -/

universe u v

open MeasureTheory TopologicalSpace

namespace Langlands.MeasureTheory

/-- A locally Zariski dense equivariant evaluation into a Noetherian space
pulls proper closed sets back to null sets. -/
def NoetherianClosedNullStatement : Prop :=
  ∀ (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (X : Type v) [TopologicalSpace X] [NoetherianSpace X]
    (μ : Measure H) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] [μ.InnerRegular]
    (f : H → X), Continuous f →
    ∀ (e : H → (X ≃ₜ X)),
      (∀ g h, f (g * h) = e g (f h)) →
      (∀ Z : Closeds X, Z ≠ ⊤ → interior (f ⁻¹' (Z : Set X)) = ∅) →
      ∀ Z : Closeds X, Z ≠ ⊤ → μ (f ⁻¹' (Z : Set X)) = 0

end Langlands.MeasureTheory
