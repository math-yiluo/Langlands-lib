import Langlands.Topology.LocallyProfinite
import Mathlib.Topology.LocallyClosed

/-!
# Renard II.1.1: statements for locally profinite spaces and groups

These proposition definitions state Van Dantzig's characterization, inheritance by locally
closed subspaces, finite disjoint compact-open refinements, and the Baire property.
All topologies are the supplied topologies; the subspace carries its actual subtype topology.
-/

open Set Filter TopologicalSpace Topology

universe uX uI

namespace Langlands.Topology.LocallyProfiniteStatements

/-- The compact-open subgroup characterization includes the source's Hausdorff condition. -/
def VanDantzig : Prop :=
  ∀ (G : Type uX) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    IsLocallyProfinite G ↔
      T2Space G ∧
        ∀ U ∈ 𝓝 (1 : G), ∃ H : OpenSubgroup G,
          IsCompact (H : Set G) ∧ (H : Set G) ⊆ U

/-- A locally closed subset, with the induced topology, is locally profinite. -/
def LocallyClosedSubspaces : Prop :=
  ∀ (X : Type uX) [TopologicalSpace X], IsLocallyProfinite X →
    ∀ Y : Set X, IsLocallyClosed Y → IsLocallyProfinite Y

/-- Every open cover of a compact subset admits a finite disjoint compact-open refinement
covering that subset. The refining sets are subsets of the ambient space. -/
def FiniteDisjointRefinement : Prop :=
  ∀ (X : Type uX) [TopologicalSpace X], IsLocallyProfinite X →
    ∀ K : Set X, IsCompact K →
      ∀ (I : Type uI) (U : I → Set X), (∀ i, IsOpen (U i)) →
        K ⊆ ⋃ i, U i →
          ∃ (n : ℕ) (V : Fin n → Set X),
            (∀ j, IsOpen (V j) ∧ IsCompact (V j)) ∧
            Pairwise (fun j k => Disjoint (V j) (V k)) ∧
            K ⊆ ⋃ j, V j ∧
            ∀ j, ∃ i, V j ⊆ U i

/-- Countable intersections of dense open subsets are dense, with no size condition on X. -/
def DenseOpenIntersections : Prop :=
  ∀ (X : Type uX) [TopologicalSpace X], IsLocallyProfinite X →
    ∀ (I : Type uI) [Countable I] (U : I → Set X),
      (∀ i, IsOpen (U i)) → (∀ i, Dense (U i)) → Dense (⋂ i, U i)

/-- The four II.1.1 results after the definition of a t.d. space. -/
def LocallyProfiniteAssertions : Prop :=
  VanDantzig.{uX} ∧ LocallyClosedSubspaces.{uX} ∧
    FiniteDisjointRefinement.{uX, uI} ∧ DenseOpenIntersections.{uX, uI}

end Langlands.Topology.LocallyProfiniteStatements
