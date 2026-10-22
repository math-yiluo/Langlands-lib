import Langlands.ClassFieldTheory.Local.ReciprocitySystem
import Langlands.Weil.Local.Assembly

/-!
# Actual local reciprocity systems in a common algebraic closure

The degree is the constructed geometric residue degree. The canonical
extension-field topologies are constructed for every finite intermediate
field, including nonnormal fields. Existence is a conclusion.
-/

noncomputable section

namespace Langlands.LocalClassField

universe u

/-- A geometrically normalized coherent system exists on every actual finite
intermediate extension of each finite p-adic field. Its norm, transfer,
conjugation, density and completion diagrams are all conclusions. -/
def CommonClosureReciprocityExistence : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    CommonClosure.NormalizedSystemExistence F (CommonClosure.canonicalData F)
      (Weil.Local.localResidueDegree F) T

/-- The normalized system on the constructed actual Weil subgroups is unique,
including its components at every nonnormal finite intermediate field. -/
def CommonClosureReciprocityUniqueness : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    CommonClosure.NormalizedSystemUniqueness F (CommonClosure.canonicalData F)
      (Weil.Local.localResidueDegree F) T

/-- Unconditional existence and uniqueness of the actual geometric local
reciprocity system, including all finite-extension compatibility diagrams. -/
def CommonClosureReciprocityTheorems : Prop :=
  CommonClosureReciprocityExistence.{u} ∧ CommonClosureReciprocityUniqueness.{u}

end Langlands.LocalClassField
