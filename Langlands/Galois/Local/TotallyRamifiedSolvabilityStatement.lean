import Langlands.ClassFieldTheory.Local.ReciprocitySystem
import Langlands.LocalField.Normalization.Definitions
import Mathlib.GroupTheory.Solvable

/-! # Solvability of totally ramified finite local Galois groups -/

namespace Langlands.PadicField

universe u

/-- The actual Galois group of a finite totally ramified Galois intermediate
extension is solvable, with total ramification expressed by canonical absolute
ramification indices. This is a proposition target, not a proof. -/
def TotallyRamifiedGaloisSolvability : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (E : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier)
    [IsGalois F.Carrier E.field],
    let n := Module.finrank F.Carrier E.field
    (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
        n * F.canonicalTopologicalData.ramificationIndex →
      Group.IsSolvable Gal(E.field/F.Carrier)

end Langlands.PadicField
