import Langlands.Representation.Geometric.ClosedSubgroupDefinitions
import Langlands.Topology.CompactOpen.NeighborhoodBasis
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Analysis.Complex.Basic

/-! Closed-subgroup Mackey-filtration targets, with all topology hypotheses explicit. -/

namespace Langlands.Geometric

universe uG uV

/-- Finite double-coset spaces admit an orbit ordering with open initial unions,
under the l-group and countability-at-infinity assumptions of BZ77 5.1. -/
def ClosedSubgroupOrbitOrdering : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
    [LocallyCompactSpace G] [T2Space G] [SigmaCompactSpace G]
    (P Q : Subgroup G),
    IsClosed (P : Set G) → IsClosed (Q : Set G) →
    Finite (DoubleCoset.Quotient (P : Set G) (Q : Set G)) →
    ∃ n : ℕ, Nonempty (OrderedDoubleCosets P Q n)

/-- The actual support filtration of restricted compact induction has the
conjugated compact-induction functors as its naturally isomorphic graded pieces.
This is BZ77 5.2 specialized to trivial localization subgroups and characters. -/
def ClosedSubgroupMackeyFiltration : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
    [LocallyCompactSpace G] [T2Space G] [SigmaCompactSpace G]
    (P Q : Subgroup G),
    IsClosed (P : Set G) → IsClosed (Q : Set G) →
    ∀ (n : ℕ) (s : OrderedDoubleCosets P Q n),
      (s.supportFiltration.{0, uG, uV} (R := ℂ)).HasGradedPieces
        (fun i => orbitPiece.{0, uG, uV} (R := ℂ) P Q (s.representative i))

/-- The finite-orbit ordering prerequisite and the natural closed-subgroup
Mackey-filtration assertion. No theorem truth is assumed in this definition. -/
def ClosedSubgroupMackeyTheorems : Prop :=
  ClosedSubgroupOrbitOrdering.{uG} ∧ ClosedSubgroupMackeyFiltration.{uG, uV}

end Langlands.Geometric
