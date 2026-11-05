import Langlands.Global.LeftCosetHaarMeasure
import Mathlib.MeasureTheory.Group.ModularCharacter

/-! # Unimodularity from a compact quotient by a discrete subgroup -/

universe u

open MeasureTheory

namespace Langlands.Global

/-- A locally compact Polish group with a compact discrete left quotient is unimodular.
This is an exact analytic prerequisite, not an assumed field of an adelic group. -/
def CompactDiscreteQuotientHaarRightInvariantStatement : Prop :=
  ∀ (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] [LocallyCompactSpace H] [PolishSpace H]
    (Γ : Subgroup H), IsDiscrete (Γ : Set H) →
      CompactSpace (LeftCosetSpace Γ) → (Measure.haar : Measure H).IsMulRightInvariant

end Langlands.Global
