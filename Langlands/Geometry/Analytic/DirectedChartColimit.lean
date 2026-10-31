import Langlands.Geometry.Analytic.AtlasSpectrumColimit
import Langlands.Geometry.Analytic.StrongAdmissibleChartDiagram
import Langlands.Geometry.Analytic.StrongSourceRestriction

/-! # Original chart colimits with full bounded strong maps -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory CategoryTheory.Limits Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation

/-- The actual original chart domains in the directed strong-map category. -/
def directedChartDiagram (A : AffinoidAtlasPresentation.{u, v, w} K) :
    IndexedAffinoidAtlas.ChartObject A.atlas ⥤ DirectedAtlasPresentation.{u, v, w} K :=
  A.chartStrongDiagram ⋙ DirectedAtlasPresentation.topChartFunctor

theorem directedChartDiagram_spaceFunctor (A : AffinoidAtlasPresentation.{u, v, w} K) :
    A.directedChartDiagram ⋙ DirectedAtlasPresentation.spaceFunctor =
      A.atlas.chartRangeDiagram := rfl

end AffinoidAtlasPresentation

namespace DirectedAtlasPresentation

variable (A : DirectedAtlasPresentation.{u, v, w} K)

/-- The cocone consists of the complete original strong chart inclusions. -/
def chartCocone : Cocone A.presentation.directedChartDiagram where
  pt := A
  ι :=
    { app := fun i => A.presentation.chartStrongInclusion i.index
      naturality := by
        intro i j h
        change (A.presentation.chartStrongMap i.index j.index
          (A.presentation.atlas.chartSubsetOfHom h)).compOfDirected
            (A.presentation.chartStrongInclusion j.index) _ _ =
          (A.presentation.chartStrongInclusion i.index).compOfDirected
            (AffinoidAtlasPresentation.StrongHom.id A.presentation) _ _
        rw [AffinoidAtlasPresentation.chartStrongInclusion,
          AffinoidAtlasPresentation.StrongHom.chartStrongMap_comp_restrictSource,
          AffinoidAtlasPresentation.StrongHom.compOfDirected_id]
        rfl }

/-- Forgetting gives exactly the original range-inclusion cocone. -/
theorem chartCocone_spaceFunctor :
    spaceFunctor.mapCocone A.chartCocone = A.presentation.atlas.chartRangeCocone := rfl

variable (s : Cocone A.presentation.directedChartDiagram)

/-- Descend the actual continuous maps of a full strong cocone. -/
def chartDescBaseMap : C(A.presentation.space, s.pt.presentation.space) :=
  (A.presentation.atlas.chartRangeDiagramCoconeIsColimit.desc
    (spaceFunctor.mapCocone s)).hom

theorem chartDescBaseMap_chart (i : A.presentation.atlas.Index)
    (x : Set.range (A.presentation.atlas.chart i)) :
    A.chartDescBaseMap s x.val = (s.ι.app ⟨i⟩).baseMap x :=
  congrArg (fun q : A.presentation.atlas.chartRangeDiagram.obj ⟨i⟩ ⟶
    s.pt.presentation.space => q x)
      (A.presentation.atlas.chartRangeDiagramCoconeIsColimit.fac
        (spaceFunctor.mapCocone s) ⟨i⟩)

/-- Admissibility of a global chart is admissibility of its full cocone leg
at the original top chart. -/
theorem chartDescBaseMap_admissible_iff (i : A.presentation.atlas.Index)
    (j : s.pt.presentation.atlas.Index) :
    A.chartDescBaseMap s '' Set.range (A.presentation.atlas.chart i) ⊆
        Set.range (s.pt.presentation.atlas.chart j) ↔
      (s.ι.app ⟨i⟩).baseMap ''
          Set.range ((A.presentation.chartPresentation i).atlas.chart
            (A.presentation.chartTopIndex i)) ⊆
        Set.range (s.pt.presentation.atlas.chart j) := by
  constructor <;> intro h <;> rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  · exact (A.chartDescBaseMap_chart s i ⟨_, ⟨x, rfl⟩⟩) ▸
      h ⟨_, ⟨x, rfl⟩, rfl⟩
  · rw [A.chartDescBaseMap_chart s i ⟨_, ⟨x, rfl⟩⟩]
    exact h ⟨_, ⟨x, rfl⟩, rfl⟩

/-- The same admissibility equivalence retains every original contained chart. -/
theorem chartDescBaseMap_contained_admissible_iff (i : A.presentation.atlas.Index)
    (c : A.presentation.atlas.ContainedChart i) (j : s.pt.presentation.atlas.Index) :
    A.chartDescBaseMap s '' Set.range (A.presentation.atlas.chart c.val) ⊆
        Set.range (s.pt.presentation.atlas.chart j) ↔
      (s.ι.app ⟨i⟩).baseMap ''
          Set.range ((A.presentation.chartPresentation i).atlas.chart c) ⊆
        Set.range (s.pt.presentation.atlas.chart j) := by
  constructor <;> intro h <;> rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  · exact (A.chartDescBaseMap_chart s i
      ⟨_, c.property ⟨x, rfl⟩⟩) ▸ h ⟨_, ⟨x, rfl⟩, rfl⟩
  · rw [A.chartDescBaseMap_chart s i ⟨_, c.property ⟨x, rfl⟩⟩]
    exact h ⟨_, ⟨x, rfl⟩, rfl⟩

/-- Descend every admissible bounded pullback from the full chart leg. -/
def chartDescPullback (i : A.presentation.atlas.Index)
    (j : s.pt.presentation.atlas.Index)
    (h : A.chartDescBaseMap s '' Set.range (A.presentation.atlas.chart i) ⊆
      Set.range (s.pt.presentation.atlas.chart j)) :
    BoundedAlgHom K (s.pt.presentation.atlas.algebra j) (A.presentation.atlas.algebra i) :=
  (s.ι.app ⟨i⟩).pullback (A.presentation.chartTopIndex i) j
    ((A.chartDescBaseMap_admissible_iff s i j).mp h)

/-- Full strong cocone naturality implies both-variable bounded naturality. -/
theorem chartDescPullback_naturality
    (i i' : A.presentation.atlas.Index) (j j' : s.pt.presentation.atlas.Index)
    (hi : Set.range (A.presentation.atlas.chart i) ⊆
      Set.range (A.presentation.atlas.chart i'))
    (hj : Set.range (s.pt.presentation.atlas.chart j) ⊆
      Set.range (s.pt.presentation.atlas.chart j'))
    (h : A.chartDescBaseMap s '' Set.range (A.presentation.atlas.chart i) ⊆
      Set.range (s.pt.presentation.atlas.chart j))
    (h' : A.chartDescBaseMap s '' Set.range (A.presentation.atlas.chart i') ⊆
      Set.range (s.pt.presentation.atlas.chart j')) :
    (A.presentation.atlas.restriction i i' hi).comp (A.chartDescPullback s i' j' h') =
      (A.chartDescPullback s i j h).comp (s.pt.presentation.atlas.restriction j j' hj) := by
  let f := A.presentation.chartStrongMap i i' hi
  let g := s.ι.app ⟨i'⟩
  let hb := (A.presentation.directedChartDiagram.obj ⟨i'⟩).directed
  have hf := f.image_chart_top (A.presentation.chartTopIndex i')
    (A.presentation.chartTop_contains i') (A.presentation.chartTopIndex i)
  have hg := (A.chartDescBaseMap_admissible_iff s i' j').mp h'
  have hc := f.comp_admissible g (A.presentation.chartTopIndex i)
    (A.presentation.chartTopIndex i') j' hf hg
  have hn : f.compOfDirected g hb s.pt.directed = s.ι.app ⟨i⟩ :=
    s.w (homOfLE (show (⟨i⟩ : IndexedAffinoidAtlas.ChartObject A.presentation.atlas) ≤
      ⟨i'⟩ from hi))
  have h₀ := (A.chartDescBaseMap_admissible_iff s i j).mp h
  have h₁ := (A.chartDescBaseMap_admissible_iff s i j').mp (h.trans hj)
  exact (f.compOfDirected_pullback g hb s.pt.directed
    (A.presentation.chartTopIndex i) (A.presentation.chartTopIndex i') j'
    hf hg hc).symm.trans
      ((AffinoidAtlasPresentation.StrongHom.pullback_congr hn _ _ hc h₁).trans
        ((s.ι.app ⟨i⟩).pullback_comp_restriction _ j j' hj h₀ h₁))

/-- The full bounded strong map descended from the original chart cocone. -/
def chartDesc : A ⟶ s.pt where
  baseMap := A.chartDescBaseMap s
  target_exists i := by
    obtain ⟨j, hj⟩ := (s.ι.app ⟨i⟩).target_exists (A.presentation.chartTopIndex i)
    exact ⟨j, (A.chartDescBaseMap_admissible_iff s i j).mpr hj⟩
  pullback := A.chartDescPullback s
  chart_comm i j h x := by
    exact ((s.ι.app ⟨i⟩).chart_comm (A.presentation.chartTopIndex i) j
      ((A.chartDescBaseMap_admissible_iff s i j).mp h) x).trans
        (A.chartDescBaseMap_chart s i ⟨_, ⟨x, rfl⟩⟩).symm
  restriction_comm := A.chartDescPullback_naturality s

/-- The descended map recovers the entire source-chart leg, including every
bounded pullback on every original contained chart. -/
theorem chartDesc_restrictSource (i : A.presentation.atlas.Index) :
    (A.chartDesc s).restrictSource i = s.ι.app ⟨i⟩ := by
  refine AffinoidAtlasPresentation.StrongHom.ext_of_directed s.pt.directed ?_ ?_
  · apply ContinuousMap.ext
    intro x
    exact A.chartDescBaseMap_chart s i x
  · intro c
    change A.presentation.atlas.ContainedChart i at c
    obtain ⟨j, hg⟩ := (s.ι.app ⟨i⟩).target_exists c
    have hglobal := (A.chartDescBaseMap_contained_admissible_iff s i c j).mpr hg
    have hres := ((A.chartDesc s).restrictSource_admissible_iff i c j).mpr hglobal
    refine ⟨j, hres, ?_⟩
    let f := A.presentation.chartStrongMap c.val i c.property
    let g := s.ι.app ⟨i⟩
    let hb := (A.presentation.directedChartDiagram.obj ⟨i⟩).directed
    have hf : f.baseMap ''
        Set.range ((A.presentation.chartPresentation c.val).atlas.chart
          (A.presentation.chartTopIndex c.val)) ⊆
        Set.range ((A.presentation.chartPresentation i).atlas.chart c) := by
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
    have hc := f.comp_admissible g (A.presentation.chartTopIndex c.val) c j hf hg
    have hn : f.compOfDirected g hb s.pt.directed = s.ι.app ⟨c.val⟩ :=
      s.w (homOfLE (show (⟨c.val⟩ : IndexedAffinoidAtlas.ChartObject A.presentation.atlas) ≤
        ⟨i⟩ from c.property))
    have hleg := (A.chartDescBaseMap_admissible_iff s c.val j).mp hglobal
    have hp := AffinoidAtlasPresentation.StrongHom.pullback_congr hn
      (A.presentation.chartTopIndex c.val) j hc hleg
    apply hp.symm.trans
    apply (f.compOfDirected_pullback g hb s.pt.directed
      (A.presentation.chartTopIndex c.val) c j hf hg hc).trans
    change (A.presentation.atlas.restriction c.val c.val _).comp
      ((s.ι.app ⟨i⟩).pullback c j hg) = (s.ι.app ⟨i⟩).pullback c j _
    exact (congrArg (fun q : BoundedAlgHom K
        (A.presentation.atlas.algebra c.val) (A.presentation.atlas.algebra c.val) =>
      q.comp ((s.ι.app ⟨i⟩).pullback c j hg))
        (A.presentation.atlas.restriction_id c.val _)).trans
          (BoundedAlgHom.id_comp _)

/-- Every full strong cocone factors through the canonical chart inclusions. -/
theorem chartCocone_fac (i : IndexedAffinoidAtlas.ChartObject A.presentation.atlas) :
    A.chartCocone.ι.app i ≫ A.chartDesc s = s.ι.app i :=
  ((A.chartDesc s).chartStrongInclusion_comp A.directed s.pt.directed i.index).trans
    (A.chartDesc_restrictSource s i.index)

/-- A directed actual atlas is the colimit of its original chart-domain
presentations in the category whose arrows retain all bounded strong data. -/
def chartCoconeIsColimit : IsColimit A.chartCocone where
  desc := A.chartDesc
  fac := A.chartCocone_fac
  uniq s m hm := by
    apply AffinoidAtlasPresentation.StrongHom.ext_of_restrictSource
    intro i
    exact (((m.chartStrongInclusion_comp A.directed s.pt.directed i).symm).trans
      (hm ⟨i⟩)).trans (A.chartDesc_restrictSource s i).symm

/-- Forgetting bounded strong data preserves this original chart colimit. -/
instance spaceFunctorPreservesChartColimit :
    PreservesColimit A.presentation.directedChartDiagram
      (spaceFunctor (K := K)) :=
  preservesColimit_of_preserves_colimit_cocone A.chartCoconeIsColimit
    A.presentation.atlas.chartRangeDiagramCoconeIsColimit

end DirectedAtlasPresentation

end Langlands.Analytic
