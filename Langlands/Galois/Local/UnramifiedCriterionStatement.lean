import Langlands.Galois.Local.AbsoluteDefinitions
import Langlands.ClassFieldTheory.Local.ReciprocitySystem
import Langlands.LocalField.Normalization.Definitions

/-! # Canonical unramified criterion using absolute inertia -/

namespace Langlands.PadicField

universe u

/-- A finite Galois intermediate extension has the same canonical absolute
ramification index as the base field exactly when absolute inertia fixes it. -/
def CanonicalUnramifiedCriterion : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (E : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier)
    [IsGalois F.Carrier E.field],
    F.canonicalTopologicalData.ramificationIndex =
        (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex ↔
      F.absoluteInertia F.canonicalTopologicalData ≤ E.field.fixingSubgroup

end Langlands.PadicField
