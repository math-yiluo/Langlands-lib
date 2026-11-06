import Langlands.LocalField.Canonical
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.Group.Units

/-! # Separation by open finite-index subgroups

An internal topological prerequisite for separation by actual norm groups.
No arithmetic realization of an open subgroup is assumed or asserted here.
-/

namespace Langlands.LocalClassField

universe u

/-- Open finite-index subgroups separate the multiplicative group of an actual
p-adic field, for every supplied local-field topology. -/
def OpenFiniteIndexSubgroupsSeparatePoints : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    let := T.topology
    ∀ a : F.Carrierˣ, a ≠ 1 →
      ∃ H : Subgroup F.Carrierˣ,
        IsOpen (H : Set F.Carrierˣ) ∧ H.FiniteIndex ∧ a ∉ H

end Langlands.LocalClassField
