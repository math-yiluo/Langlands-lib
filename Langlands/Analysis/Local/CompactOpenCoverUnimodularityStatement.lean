import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Two-sided Haar invariance from a cover by compact open subgroups

This proposition states right invariance of every regular left Haar measure on a
locally compact Hausdorff group whose elements all lie in compact open subgroups,
and on every closed subgroup of such a group with its subspace topology.
-/

namespace Langlands.Haar

open MeasureTheory MeasureTheory.Measure

universe uG

/-- If every element of a locally compact Hausdorff topological group `G` lies in a
compact open subgroup, then every regular left Haar measure on `G`, and every regular
left Haar measure on every closed subgroup of `G` with its subspace topology, is
invariant under every right translation. -/
def CompactOpenCoverUnimodularityStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G],
    (∀ g : G, ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ g ∈ K) →
      (∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
          [IsHaarMeasure μ] [μ.Regular], IsMulRightInvariant μ) ∧
      ∀ (H : Subgroup G), IsClosed (H : Set G) →
        ∀ [MeasurableSpace H] [BorelSpace H] (μH : Measure H)
          [IsHaarMeasure μH] [μH.Regular], IsMulRightInvariant μH

end Langlands.Haar
