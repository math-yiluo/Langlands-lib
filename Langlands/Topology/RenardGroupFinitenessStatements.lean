import Langlands.Topology.LocallyProfinite
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Renard II.3.2: finiteness, discreteness and countability of coset quotients

These proposition definitions state the three conclusions at the source's t.d.
topological-group scope. All coset spaces and topologies are the actual subgroup
quotients of the supplied groups and topological spaces.
-/

set_option autoImplicit false

universe u

namespace Langlands.Topology.RenardGroupFinitenessStatements

/-- Nested compact open subgroups have a finite relative coset quotient. -/
def RelativeQuotientFinite : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    IsLocallyProfinite G →
      ∀ K K1 : Subgroup G,
        IsCompact (K : Set G) → IsOpen (K : Set G) →
          IsCompact (K1 : Set G) → IsOpen (K1 : Set G) → K ≤ K1 →
            Finite (K1 ⧸ K.subgroupOf K1)

/-- The ordinary coset quotient by a compact open subgroup is discrete. -/
def QuotientDiscrete : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    IsLocallyProfinite G →
      ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
        DiscreteTopology (G ⧸ K)

/-- Sigma-compactness makes the same coset quotient countable. -/
def QuotientCountable : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SigmaCompactSpace G],
    IsLocallyProfinite G →
      ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
        Countable (G ⧸ K)

/-- All three conclusions of Renard II.3.2, with sigma-compactness only in the last. -/
def Assertions : Prop :=
  RelativeQuotientFinite.{u} ∧ QuotientDiscrete.{u} ∧ QuotientCountable.{u}

end Langlands.Topology.RenardGroupFinitenessStatements
