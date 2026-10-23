import Langlands.Galois.Local.AbsoluteDefinitions
import Langlands.ClassFieldTheory.Local.ReciprocitySystem
import Langlands.LocalField.Normalization.Definitions
import Mathlib.FieldTheory.LinearDisjoint

/-! # Total ramification from disjointness with the inertia fixed field -/

namespace Langlands.PadicField

universe u

/-- A finite intermediate extension linearly disjoint from the actual canonical
inertia fixed field is totally ramified, expressed by absolute indices. -/
def InertiaDisjointTotallyRamified : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (D : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier),
    let U := IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)
    D.field.LinearDisjoint U →
      (D.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
        Module.finrank F.Carrier D.field * F.canonicalTopologicalData.ramificationIndex

end Langlands.PadicField
