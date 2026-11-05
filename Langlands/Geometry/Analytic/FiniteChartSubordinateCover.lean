import Langlands.Geometry.Analytic.FiniteChartCoverComparison
import Langlands.Geometry.Analytic.AtlasDomainChartCover

/-! # Subordinate original-chart covers inside Hausdorff finite unions -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData

open Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  (d : FiniteChartGluingData a)

/-- Compact cross intersections suffice: the net refines each intersection,
and the finite disjoint union of those finite families covers the parent. -/
def subordinateCoverOfCompactIntersections (parent : a.Index)
    (hparent : Set.range (a.chart parent) ⊆ d.locus)
    (hc : ∀ i : Fin d.size, IsCompact
      (Set.range (a.chart parent) ∩ Set.range (a.chart (d.index i)))) :
    d.SubordinateChartCover parent := by
  classical
  let c (i : Fin d.size) :=
    a.compactIntersectionChartCover parent (d.index i)
      (Set.range (a.chart parent) ∩ Set.range (a.chart (d.index i)))
      (hc i) Subset.rfl
  let T := (i : Fin d.size) × Fin (c i).size
  let e : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  refine {
    size := Fintype.card T
    index := fun t => (c (e t).1).index (e t).2
    member := fun t => (e t).1
    subset_parent := fun t => (c (e t).1).left_subset (e t).2
    subset_member := fun t => (c (e t).1).right_subset (e t).2
    covers := ?_ }
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hparent hx)
  obtain ⟨t, ht⟩ := (c i).covers x ⟨hx, hi⟩
  apply Set.mem_iUnion.mpr
  refine ⟨e.symm ⟨i, t⟩, ?_⟩
  rw [e.apply_symm_apply]
  exact ht

/-- Both original charts lie in the Hausdorff literal union, so their
compact images intersect compactly in that subspace and hence in X. -/
theorem isCompact_inter_member [T2Space d.locus] (parent : a.Index)
    (hparent : Set.range (a.chart parent) ⊆ d.locus) (i : Fin d.size) :
    IsCompact (Set.range (a.chart parent) ∩ Set.range (a.chart (d.index i))) := by
  have hp : IsCompact
      (Subtype.val ⁻¹' Set.range (a.chart parent) : Set d.locus) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage'
      (isCompact_range (a.isEmbedding_chart parent).continuous)
      (by simpa only [Subtype.range_coe] using hparent)
  have hi : IsCompact
      (Subtype.val ⁻¹' Set.range (a.chart (d.index i)) : Set d.locus) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage'
      (isCompact_range (a.isEmbedding_chart (d.index i)).continuous)
      (by
        simpa only [Subtype.range_coe, locus] using
          (Set.subset_iUnion (fun j => Set.range (a.chart (d.index j))) i))
  have heq : Subtype.val ''
      ((Subtype.val ⁻¹' Set.range (a.chart parent) : Set d.locus) ∩
        Subtype.val ⁻¹' Set.range (a.chart (d.index i))) =
      Set.range (a.chart parent) ∩ Set.range (a.chart (d.index i)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hparent hx.1⟩, hx, rfl⟩
  rw [← heq]
  exact (hp.inter hi).image continuous_subtype_val

/-- Every original chart contained in a Hausdorff finite union has a
finite cover by original charts subordinate to its defining family. -/
def subordinateCoverOfHausdorff [T2Space d.locus] (parent : a.Index)
    (hparent : Set.range (a.chart parent) ⊆ d.locus) :
    d.SubordinateChartCover parent :=
  d.subordinateCoverOfCompactIntersections parent hparent
    (d.isCompact_inter_member parent hparent)

/-- No cross-intersection chart or subordinate cover is supplied: the
bounded map to each contained original chart is constructed by descent. -/
def originalRestriction [T2Space d.locus] (parent : a.Index)
    (hparent : Set.range (a.chart parent) ⊆ d.locus) :
    BoundedAlgHom K d.SectionAlgebra (a.algebra parent) :=
  (d.subordinateCoverOfHausdorff parent hparent).restriction

/-- The constructed map recovers every original restriction formula on
every common original subchart, including the full algebra map. -/
theorem original_comp_originalRestriction [T2Space d.locus] (parent : a.Index)
    (hparent : Set.range (a.chart parent) ⊆ d.locus) (k : a.Index)
    (hkp : Set.range (a.chart k) ⊆ Set.range (a.chart parent)) (i : Fin d.size)
    (hki : Set.range (a.chart k) ⊆ Set.range (a.chart (d.index i))) :
    (a.restriction k parent hkp).comp (d.originalRestriction parent hparent) =
      (a.restriction k (d.index i) hki).comp (d.projection i) :=
  (d.subordinateCoverOfHausdorff parent hparent).restriction_original k hkp i hki

/-- Original-chart inclusion commutes with the constructed bounded maps. -/
theorem originalRestriction_naturality [T2Space d.locus] (parent child : a.Index)
    (hparent : Set.range (a.chart parent) ⊆ d.locus)
    (hchild : Set.range (a.chart child) ⊆ d.locus)
    (h : Set.range (a.chart child) ⊆ Set.range (a.chart parent)) :
    (a.restriction child parent h).comp (d.originalRestriction parent hparent) =
      d.originalRestriction child hchild :=
  (d.subordinateCoverOfHausdorff parent hparent).restriction_naturality
    (d.subordinateCoverOfHausdorff child hchild) h

end Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData
