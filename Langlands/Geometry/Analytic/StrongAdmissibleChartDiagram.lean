import Langlands.Geometry.Analytic.AtlasSpectrumDiagram
import Langlands.Geometry.Analytic.StrongChartDomainComposition
import Langlands.Geometry.Analytic.DirectedAtlasComposition

/-! # Full strong maps on the order of all admissible chart pairs -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation

variable (A : AffinoidAtlasPresentation.{u, v, w} K)

/-- The original chart-domain presentations with full strong inclusions. -/
def chartStrongDiagram :
    IndexedAffinoidAtlas.ChartObject A.atlas ⥤ TopChartPresentation.{u, v, w} K where
  obj i := TopChartPresentation.ofChart A i.index
  map h := A.chartStrongMap _ _ (A.atlas.chartSubsetOfHom h)
  map_id i := A.chartStrongMap_id i.index _
  map_comp {_i _j _k} _h _g := (A.chartStrongMap_comp _ _ _ _ _ _).symm

/-- Forgetting the full strong diagram gives the original range subspaces. -/
theorem chartStrongDiagram_spaceFunctor :
    A.chartStrongDiagram ⋙ TopChartPresentation.spaceFunctor =
      A.atlas.chartRangeDiagram := rfl

namespace StrongHom

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}

/-- All pairs of original charts for which the source image is contained in
the target chart. Neither a selected target function nor monotonicity is needed. -/
def AdmissibleChartPair (f : StrongHom A B) :=
  {p : IndexedAffinoidAtlas.ChartObject A.atlas ×
      IndexedAffinoidAtlas.ChartObject B.atlas //
    f.baseMap '' Set.range (A.atlas.chart p.1.index) ⊆
      Set.range (B.atlas.chart p.2.index)}

instance (f : StrongHom A B) : PartialOrder f.AdmissibleChartPair :=
  inferInstanceAs (PartialOrder
    {p : IndexedAffinoidAtlas.ChartObject A.atlas ×
        IndexedAffinoidAtlas.ChartObject B.atlas //
      f.baseMap '' Set.range (A.atlas.chart p.1.index) ⊆
        Set.range (B.atlas.chart p.2.index)})

/-- Projection to the actual source chart order. -/
def chartPairSource (f : StrongHom A B) :
    f.AdmissibleChartPair ⥤ IndexedAffinoidAtlas.ChartObject A.atlas where
  obj p := p.val.1
  map h := homOfLE (leOfHom h).1

/-- Projection to the actual target chart order. -/
def chartPairTarget (f : StrongHom A B) :
    f.AdmissibleChartPair ⥤ IndexedAffinoidAtlas.ChartObject B.atlas where
  obj p := p.val.2
  map h := homOfLE (leOfHom h).2

/-- All admissible chart restrictions form one natural transformation of
actual chart-domain presentations and full bounded strong maps. -/
def chartRestrictionTransformation (f : StrongHom A B) :
    f.chartPairSource ⋙ A.chartStrongDiagram ⟶
      f.chartPairTarget ⋙ B.chartStrongDiagram where
  app p := f.onCharts p.val.1.index p.val.2.index p.property
  naturality p q h := by
    have hi := (leOfHom h).1
    have hj := (leOfHom h).2
    exact (f.chartStrongMap_onCharts p.val.1.index q.val.1.index q.val.2.index
      hi (p.property.trans hj) q.property).trans
        (f.onCharts_chartStrongMap p.val.1.index p.val.2.index q.val.2.index
          hj p.property (p.property.trans hj)).symm

/-- The same all-admissible data, as bounded maps in the opposite category
of genuine presented affinoid algebras. -/
def chartPairAffinoidTransformation (f : StrongHom A B) :
    f.chartPairSource ⋙ A.atlas.chartAffinoidDiagram ⟶
      f.chartPairTarget ⋙ B.atlas.chartAffinoidDiagram where
  app p := Quiver.Hom.op (show B.atlas.algebra p.val.2.index ⟶
    A.atlas.algebra p.val.1.index from f.pullback _ _ p.property)
  naturality p q h := by
    apply Quiver.Hom.unop_inj
    exact f.restriction_comm p.val.1.index q.val.1.index p.val.2.index q.val.2.index
      (leOfHom h).1 (leOfHom h).2 p.property q.property

/-- Actual maps of chart spectra induced by every admissible bounded map. -/
def chartPairSpectrumTransformation (f : StrongHom A B) :
    f.chartPairSource ⋙ A.atlas.chartSpectrumDiagram ⟶
      f.chartPairTarget ⋙ B.atlas.chartSpectrumDiagram :=
  Functor.whiskerRight f.chartPairAffinoidTransformation (affinoidSpectrumFunctor K)

/-- The ambient continuous map on every admissible pair of chart ranges. -/
def chartPairRangeTransformation (f : StrongHom A B) :
    f.chartPairSource ⋙ A.atlas.chartRangeDiagram ⟶
      f.chartPairTarget ⋙ B.atlas.chartRangeDiagram where
  app p := TopCat.ofHom (f.restrictBaseMap _ _ p.property)
  naturality _ _ _ := rfl

/-- The strong restriction transformation retains the exact original
continuous maps after forgetting the bounded algebra data. -/
theorem chartRestrictionTransformation_spaceFunctor (f : StrongHom A B) :
    Functor.whiskerRight f.chartRestrictionTransformation
        TopChartPresentation.spaceFunctor =
      f.chartPairRangeTransformation := rfl

/-- The actual spectrum/range comparisons intertwine every admissible
bounded pullback with the restricted ambient map. -/
theorem chartPairSpectrumRange_naturality (f : StrongHom A B)
    (p : f.AdmissibleChartPair) :
    TopCat.uliftFunctor.{v}.map (f.chartPairSpectrumTransformation.app p) ≫
        B.atlas.chartSpectrumRangeIso.hom.app p.val.2 =
      A.atlas.chartSpectrumRangeIso.hom.app p.val.1 ≫
        TopCat.uliftFunctor.{u}.map (f.chartPairRangeTransformation.app p) := by
  apply TopCat.ext
  intro x
  apply ULift.ext
  apply Subtype.ext
  exact f.chart_comm p.val.1.index p.val.2.index p.property x.down

/-- Restricting directed ambient composition to any admissible chain
equals the categorical composite of the full local chart restrictions. -/
theorem onCharts_compOfDirected (f : StrongHom A B) (g : StrongHom B C)
    (hb : B.atlas.HasDirectedCharts) (hc : C.atlas.HasDirectedCharts)
    (i : A.atlas.Index) (j : B.atlas.Index) (k : C.atlas.Index)
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hg : g.baseMap '' Set.range (B.atlas.chart j) ⊆ Set.range (C.atlas.chart k))
    (h : (f.compOfDirected g hb hc).baseMap '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k)) :
    (f.compOfDirected g hb hc).onCharts i k h =
      f.onCharts i j hf ≫ g.onCharts j k hg := by
  apply toChosen_injective (C.chartTopIndex k) (C.chartTop_contains k)
  refine Hom.ext rfl rfl ?_
  apply heq_of_eq
  funext a
  exact (f.compOfDirected_pullback g hb hc a.val j k
    ((Set.image_mono a.property).trans hf) hg
    ((Set.image_mono a.property).trans h)).trans
      ((f.onCharts i j hf).compOfTopCharts_pullback_top (g.onCharts j k hg)
        (B.chartTopIndex j) (B.chartTop_contains j)
        (C.chartTopIndex k) (C.chartTop_contains k) a).symm

/-- Full local composition is independent of the admissible intermediate
original chart. Equality includes every bounded local pullback. -/
theorem onCharts_comp_independent (f : StrongHom A B) (g : StrongHom B C)
    (hb : B.atlas.HasDirectedCharts) (hc : C.atlas.HasDirectedCharts)
    (i : A.atlas.Index) (j j' : B.atlas.Index) (k : C.atlas.Index)
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hf' : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j'))
    (hg : g.baseMap '' Set.range (B.atlas.chart j) ⊆ Set.range (C.atlas.chart k))
    (hg' : g.baseMap '' Set.range (B.atlas.chart j') ⊆ Set.range (C.atlas.chart k)) :
    f.onCharts i j hf ≫ g.onCharts j k hg =
      f.onCharts i j' hf' ≫ g.onCharts j' k hg' :=
  (f.onCharts_compOfDirected g hb hc i j k hf hg
    (f.comp_admissible g i j k hf hg)).symm.trans
      (f.onCharts_compOfDirected g hb hc i j' k hf' hg'
        (f.comp_admissible g i j k hf hg))

/-- Equality of one full local restriction per original source chart
determines the entire strong map to a directed target. Ambient-map equality
is derived from chart coverage rather than assumed. -/
theorem ext_of_onCharts {f g : StrongHom A B} (hb : B.atlas.HasDirectedCharts)
    (hlocal : ∀ i, ∃ (j : B.atlas.Index)
      (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
      (hg : g.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)),
      f.onCharts i j hf = g.onCharts i j hg) : f = g := by
  have hbase : f.baseMap = g.baseMap := by
    apply ContinuousMap.ext
    intro x
    have hx : x ∈ ⋃₀ Set.range (fun i => Set.range (A.atlas.chart i)) := by
      rw [A.atlas.isNet_chartFamily.1.covers]
      exact Set.mem_univ x
    obtain ⟨_, ⟨i, rfl⟩, y, rfl⟩ := Set.mem_sUnion.mp hx
    obtain ⟨j, hf, hg, heq⟩ := hlocal i
    exact congrArg
      (fun q : TopChartPresentation.ofChart A i ⟶ TopChartPresentation.ofChart B j =>
        (q.baseMap ⟨A.atlas.chart i y, ⟨y, rfl⟩⟩).val) heq
  refine ext_of_directed hb hbase ?_
  intro i
  obtain ⟨j, hf, hg, heq⟩ := hlocal i
  refine ⟨j, hf, ?_⟩
  have hp := congrArg (fun q : TopChartPresentation.ofChart A i ⟶
      TopChartPresentation.ofChart B j =>
    (q.pullback (A.chartTopIndex i) (B.chartTopIndex j)
      (q.image_chart_top (B.chartTopIndex j) (B.chartTop_contains j)
        (A.chartTopIndex i)) :
        BoundedAlgHom K (B.atlas.algebra j) (A.atlas.algebra i))) heq
  exact hp

end StrongHom

end AffinoidAtlasPresentation

end Langlands.Analytic
