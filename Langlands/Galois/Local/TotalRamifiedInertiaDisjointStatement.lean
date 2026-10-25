import Langlands.Galois.Local.AbsoluteDefinitions
import Langlands.ClassFieldTheory.Local.ReciprocitySystem
import Langlands.LocalField.Normalization.Definitions
import Mathlib.FieldTheory.LinearDisjoint

/-! # Disjointness of a totally ramified field and the inertia fixed field -/

namespace Langlands.PadicField

universe u

/-- A finite Galois intermediate extension whose canonical absolute index
expresses total ramification is linearly disjoint from the actual canonical
inertia fixed field in the same algebraic closure. -/
def TotallyRamifiedInertiaDisjoint : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (D : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier)
    [IsGalois F.Carrier D.field],
    (D.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
        Module.finrank F.Carrier D.field * F.canonicalTopologicalData.ramificationIndex →
      D.field.LinearDisjoint
        (IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData))

end Langlands.PadicField
