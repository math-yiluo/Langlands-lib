import Langlands.Geometry.Analytic.StrongChartDomainComposition
import Langlands.Geometry.Analytic.DirectedAtlasComposition

/-! # Full strong restriction to an actual source chart domain -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}

namespace StrongHom

/-- Restricting only the source retains exactly original admissibility. -/
theorem restrictSource_admissible_iff (f : StrongHom A B) (i : A.atlas.Index)
    (c : A.atlas.ContainedChart i) (j : B.atlas.Index) :
    (f.baseMap.comp (A.chartInclusion i).baseMap) ''
        Set.range ((A.chartPresentation i).atlas.chart c) ⊆
          Set.range (B.atlas.chart j) ↔
      f.baseMap '' Set.range (A.atlas.chart c.val) ⊆
        Set.range (B.atlas.chart j) := by
  constructor <;> intro h <;> rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  · exact h ⟨_, ⟨x, rfl⟩, rfl⟩
  · exact h ⟨_, ⟨x, rfl⟩, rfl⟩

/-- Restrict a full strong map to one actual source chart domain, keeping
the entire original target atlas and all original admissible bounded maps. -/
def restrictSource (f : StrongHom A B) (i : A.atlas.Index) :
    StrongHom (A.chartPresentation i) B where
  baseMap := f.baseMap.comp (A.chartInclusion i).baseMap
  target_exists c := by
    obtain ⟨j, hj⟩ := f.target_exists c.val
    exact ⟨j, (f.restrictSource_admissible_iff i c j).mpr hj⟩
  pullback c j h := f.pullback c.val j
    ((f.restrictSource_admissible_iff i c j).mp h)
  chart_comm c j h x := f.chart_comm c.val j _ x
  restriction_comm c c' j j' hc hj h h' :=
    f.restriction_comm c.val c'.val j j'
      (A.atlas.chart_subset_of_containedSubset i c c' hc) hj
      ((f.restrictSource_admissible_iff i c j).mp h)
      ((f.restrictSource_admissible_iff i c' j').mp h')

@[simp]
theorem restrictSource_apply (f : StrongHom A B) (i : A.atlas.Index)
    (x : Set.range (A.atlas.chart i)) :
    (f.restrictSource i).baseMap x = f.baseMap x.val := rfl

/-- This retains the original bounded map, including nonreduced algebra data. -/
theorem restrictSource_pullback (f : StrongHom A B) (i : A.atlas.Index)
    (c : A.atlas.ContainedChart i) (j : B.atlas.Index)
    (h : (f.restrictSource i).baseMap ''
      Set.range ((A.chartPresentation i).atlas.chart c) ⊆ Set.range (B.atlas.chart j)) :
    (f.restrictSource i).pullback c j h =
      f.pullback c.val j ((f.restrictSource_admissible_iff i c j).mp h) := rfl

/-- Equality of complete strong maps preserves every fixed bounded pullback. -/
theorem pullback_congr {f g : StrongHom A B} (heq : f = g)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hg : g.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    f.pullback i j hf = g.pullback i j hg := by
  subst g
  rfl

/-- Full source-chart restrictions detect global strong equality without
directedness or any chosen target charts. -/
theorem ext_of_restrictSource {f g : StrongHom A B}
    (hlocal : ∀ i, f.restrictSource i = g.restrictSource i) : f = g := by
  have hbase : f.baseMap = g.baseMap := by
    apply ContinuousMap.ext
    intro x
    have hx : x ∈ ⋃₀ Set.range (fun i => Set.range (A.atlas.chart i)) := by
      rw [A.atlas.isNet_chartFamily.1.covers]
      exact Set.mem_univ x
    obtain ⟨_, ⟨i, rfl⟩, y, rfl⟩ := Set.mem_sUnion.mp hx
    exact congrArg (fun q : StrongHom (A.chartPresentation i) B =>
      q.baseMap ⟨A.atlas.chart i y, ⟨y, rfl⟩⟩) (hlocal i)
  rcases f with ⟨fb, ft, fp, fc, fr⟩
  rcases g with ⟨gb, gt, gp, gc, gr⟩
  dsimp only [baseMap] at hbase
  subst gb
  refine StrongHom.ext rfl ?_
  apply heq_of_eq
  funext i j h
  exact pullback_congr (hlocal i) (A.chartTopIndex i) j
    ((restrictSource_admissible_iff _ i (A.chartTopIndex i) j).mpr h)
    ((restrictSource_admissible_iff _ i (A.chartTopIndex i) j).mpr h)

/-- Source restriction commutes with actual directed composition, as equality
of every admissible bounded map. No directedness of the source is needed. -/
theorem restrictSource_compOfDirected (f : StrongHom A B) (g : StrongHom B C)
    (hb : B.atlas.HasDirectedCharts) (hc : C.atlas.HasDirectedCharts)
    (i : A.atlas.Index) :
    (f.compOfDirected g hb hc).restrictSource i =
      (f.restrictSource i).compOfDirected g hb hc := by
  refine ext_of_directed hc rfl ?_
  intro a
  change A.atlas.ContainedChart i at a
  obtain ⟨j, hf⟩ := f.target_exists a.val
  obtain ⟨k, hg⟩ := g.target_exists j
  have hf' := (f.restrictSource_admissible_iff i a j).mpr hf
  have h := (f.restrictSource i).comp_admissible g a j k hf' hg
  refine ⟨k, h, ?_⟩
  change (f.compOfDirected g hb hc).pullback a.val k
    (f.comp_admissible g a.val j k hf hg) = _
  exact (f.compOfDirected_pullback g hb hc a.val j k hf hg
    (f.comp_admissible g a.val j k hf hg)).trans
      ((f.restrictSource i).compOfDirected_pullback g hb hc a j k hf' hg h).symm

end StrongHom

/-- The actual source-domain inclusion retains every original admissible
bounded restriction, without requiring a directed ambient atlas. -/
def chartStrongInclusion (A : AffinoidAtlasPresentation.{u, v, w} K)
    (i : A.atlas.Index) : StrongHom (A.chartPresentation i) A :=
  (StrongHom.id A).restrictSource i

@[simp]
theorem chartStrongInclusion_apply (i : A.atlas.Index)
    (x : Set.range (A.atlas.chart i)) :
    (A.chartStrongInclusion i).baseMap x = x.val := rfl

/-- At a directed ambient atlas this is exactly the existing extension of
the original chosen inclusion. -/
theorem chartStrongInclusion_eq_ofDirected (ha : A.atlas.HasDirectedCharts)
    (i : A.atlas.Index) :
    A.chartStrongInclusion i = StrongHom.ofDirected (A.chartInclusion i) ha := by
  apply StrongHom.eq_ofDirected_of_pullback_selected _ ha _ rfl
  intro c
  change A.atlas.restriction c.val c.val _ = BoundedAlgHom.id K (A.atlas.algebra c.val)
  exact A.atlas.restriction_id c.val _

namespace StrongHom

/-- The actual chart inclusion followed by the full global map is its
source-only restriction. -/
theorem chartStrongInclusion_comp (f : StrongHom A B)
    (ha : A.atlas.HasDirectedCharts) (hb : B.atlas.HasDirectedCharts)
    (i : A.atlas.Index) :
    (A.chartStrongInclusion i).compOfDirected f ha hb = f.restrictSource i := by
  rw [chartStrongInclusion, ← restrictSource_compOfDirected, id_compOfDirected]

set_option maxHeartbeats 800000 in
/-- Nested original source chart inclusions commute with source-only
restriction to a directed target, retaining all target charts. -/
theorem chartStrongMap_comp_restrictSource (f : StrongHom A B)
    (hb : B.atlas.HasDirectedCharts) (i i' : A.atlas.Index)
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i')) :
    (A.chartStrongMap i i' hi).compOfDirected (f.restrictSource i')
        ((A.chartPresentation i').atlas.hasDirectedCharts_of_top
          (A.chartTopIndex i') (A.chartTop_contains i')) hb =
      f.restrictSource i := by
  refine ext_of_directed hb rfl ?_
  intro a
  change A.atlas.ContainedChart i at a
  let a' : A.atlas.ContainedChart i' := ⟨a.val, a.property.trans hi⟩
  obtain ⟨j, hj⟩ := f.target_exists a.val
  have hf : (A.chartStrongMap i i' hi).baseMap ''
      Set.range ((A.chartPresentation i).atlas.chart a) ⊆
        Set.range ((A.chartPresentation i').atlas.chart a') := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have hg := (f.restrictSource_admissible_iff i' a' j).mpr hj
  have h := (A.chartStrongMap i i' hi).comp_admissible (f.restrictSource i')
    a a' j hf hg
  refine ⟨j, h, ?_⟩
  have hp := (A.chartStrongMap i i' hi).compOfDirected_pullback (f.restrictSource i')
    ((A.chartPresentation i').atlas.hasDirectedCharts_of_top
      (A.chartTopIndex i') (A.chartTop_contains i')) hb a a' j hf hg h
  refine hp.trans ?_
  change (A.atlas.restriction a.val a.val _).comp (f.pullback a.val j _) =
    f.pullback a.val j _
  rw [A.atlas.restriction_id, BoundedAlgHom.id_comp]

/-- Restricting both source and target, then including the target chart,
recovers the full source-only restriction. -/
theorem onCharts_comp_chartStrongInclusion (f : StrongHom A B)
    (hb : B.atlas.HasDirectedCharts) (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    (f.onCharts i j h).compOfDirected (B.chartStrongInclusion j)
        ((B.chartPresentation j).atlas.hasDirectedCharts_of_top
          (B.chartTopIndex j) (B.chartTop_contains j)) hb =
      f.restrictSource i := by
  refine ext_of_directed hb rfl ?_
  intro a
  change A.atlas.ContainedChart i at a
  have hf := (f.onCharts i j h).image_chart_top
    (B.chartTopIndex j) (B.chartTop_contains j) a
  have hg : (B.chartStrongInclusion j).baseMap ''
      Set.range ((B.chartPresentation j).atlas.chart (B.chartTopIndex j)) ⊆
        Set.range (B.atlas.chart j) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have hh := (f.onCharts i j h).comp_admissible (B.chartStrongInclusion j)
    a (B.chartTopIndex j) j hf hg
  refine ⟨j, hh, ?_⟩
  have hp := (f.onCharts i j h).compOfDirected_pullback (B.chartStrongInclusion j)
    ((B.chartPresentation j).atlas.hasDirectedCharts_of_top
      (B.chartTopIndex j) (B.chartTop_contains j)) hb a (B.chartTopIndex j) j hf hg hh
  refine hp.trans ?_
  have hfa : f.baseMap '' Set.range (A.atlas.chart a.val) ⊆
      Set.range (B.atlas.chart j) := (Set.image_mono a.property).trans h
  change (f.pullback a.val j hfa).comp (B.atlas.restriction j j Subset.rfl) =
    f.pullback a.val j hfa
  exact (congrArg (fun q : BoundedAlgHom K (B.atlas.algebra j) (B.atlas.algebra j) =>
    (f.pullback a.val j hfa).comp q) (B.atlas.restriction_id j Subset.rfl)).trans
      (BoundedAlgHom.comp_id _)

end StrongHom

end Langlands.Analytic.AffinoidAtlasPresentation
