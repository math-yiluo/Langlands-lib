import Langlands.Geometry.Analytic.StrongAtlasRestriction
import Langlands.Geometry.Analytic.StrongAtlasComposition

/-! # Full strong composition on actual chart domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation

open CategoryTheory Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}

namespace StrongHom

/-- At the greatest target, the full composite pullback factors through the
greatest intermediate chart. -/
theorem compOfTopCharts_pullback_top (f : StrongHom A B) (g : StrongHom B C)
    (b : B.atlas.Index)
    (hb : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart b))
    (c : C.atlas.Index)
    (hc : ∀ j, Set.range (C.atlas.chart j) ⊆ Set.range (C.atlas.chart c))
    (i : A.atlas.Index) :
    (f.compOfTopCharts g b hb c hc).pullback i c
        ((f.compOfTopCharts g b hb c hc).image_chart_top c hc i) =
      (f.pullback i b (f.image_chart_top b hb i)).comp
        (g.pullback b c (g.image_chart_top c hc b)) :=
  f.compOfTopCharts_pullback g b hb c hc i b c
    (f.image_chart_top b hb i) (g.image_chart_top c hc b)
    ((f.compOfTopCharts g b hb c hc).image_chart_top c hc i)

/-- Regard each arbitrary admissible restriction as a morphism in the actual
greatest-chart category, without a greatest-chart premise on the ambient atlases. -/
def onCharts (f : StrongHom A B) (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    TopChartPresentation.ofChart A i ⟶ TopChartPresentation.ofChart B j :=
  f.restrictChart i j h

/-- Local composition uses the specified admissible intermediate chart.
It agrees with restriction of the existing ambient greatest-chart composite. -/
theorem onCharts_compOfTopCharts (f : StrongHom A B) (g : StrongHom B C)
    (b : B.atlas.Index)
    (hb : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart b))
    (c : C.atlas.Index)
    (hc : ∀ j, Set.range (C.atlas.chart j) ⊆ Set.range (C.atlas.chart c))
    (i : A.atlas.Index) (j : B.atlas.Index) (k : C.atlas.Index)
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hg : g.baseMap '' Set.range (B.atlas.chart j) ⊆ Set.range (C.atlas.chart k))
    (h : (f.compOfTopCharts g b hb c hc).baseMap '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k)) :
    (f.compOfTopCharts g b hb c hc).onCharts i k h =
      f.onCharts i j hf ≫ g.onCharts j k hg := by
  apply toChosen_injective (C.chartTopIndex k) (C.chartTop_contains k)
  refine Hom.ext rfl rfl ?_
  apply heq_of_eq
  funext a
  exact (f.compOfTopCharts_pullback g b hb c hc a.val j k
    ((Set.image_mono a.property).trans hf) hg
    ((Set.image_mono a.property).trans h)).trans
      ((f.onCharts i j hf).compOfTopCharts_pullback_top (g.onCharts j k hg)
        (B.chartTopIndex j) (B.chartTop_contains j)
        (C.chartTopIndex k) (C.chartTop_contains k)
        a).symm

end StrongHom

/-- An actual nested chart inclusion with every admissible bounded restriction. -/
def chartStrongMap (A : AffinoidAtlasPresentation.{u, v, w} K)
    (i j : A.atlas.Index)
    (hij : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart j)) :
    TopChartPresentation.ofChart A i ⟶ TopChartPresentation.ofChart A j :=
  (StrongHom.id A).onCharts i j (by
    change (id : A.space → A.space) '' _ ⊆ _
    simpa only [Set.image_id] using hij)

@[simp]
theorem chartStrongMap_apply_val (i j : A.atlas.Index)
    (hij : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart j))
    (x : Set.range (A.atlas.chart i)) :
    ((A.chartStrongMap i j hij).baseMap x).val = x.val := rfl

/-- The full chart inclusion retains the original actual algebra restriction. -/
theorem chartStrongMap_pullback (i j : A.atlas.Index)
    (hij : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart j))
    (a : A.atlas.ContainedChart i) (b : A.atlas.ContainedChart j)
    (h : (A.chartStrongMap i j hij).baseMap ''
      Set.range ((A.chartPresentation i).atlas.chart a) ⊆
        Set.range ((A.chartPresentation j).atlas.chart b)) :
    (A.chartStrongMap i j hij).pullback a b h =
      A.atlas.restriction a.val b.val
        (by
          have hh := ((StrongHom.id A).restrictBaseMap_admissible_iff i j
            (by
              change (id : A.space → A.space) '' _ ⊆ _
              simpa only [Set.image_id] using hij) a b).mp h
          change (id : A.space → A.space) '' _ ⊆ _ at hh
          simpa only [Set.image_id] using hh) := rfl

@[simp]
theorem chartStrongMap_id (i : A.atlas.Index)
    (hii : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i)) :
    A.chartStrongMap i i hii = 𝟙 (TopChartPresentation.ofChart A i) :=
  StrongHom.restrictChart_id (A := A) i _

/-- Full strong chart inclusions compose as the actual domain inclusions. -/
theorem chartStrongMap_comp (i j k : A.atlas.Index)
    (hij : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart j))
    (hjk : Set.range (A.atlas.chart j) ⊆ Set.range (A.atlas.chart k))
    (hik : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart k)) :
    A.chartStrongMap i j hij ≫ A.chartStrongMap j k hjk =
      A.chartStrongMap i k hik := by
  apply StrongHom.toChosen_injective (A.chartTopIndex k) (A.chartTop_contains k)
  refine Hom.ext rfl rfl ?_
  apply heq_of_eq
  funext a
  exact ((A.chartStrongMap i j hij).compOfTopCharts_pullback_top
    (A.chartStrongMap j k hjk) (A.chartTopIndex j) (A.chartTop_contains j)
    (A.chartTopIndex k) (A.chartTop_contains k) a).trans
      (A.atlas.restriction_comp a.val j k (a.property.trans hij) hjk
        (a.property.trans hik)).symm

namespace StrongHom

/-- Source-domain inclusion commutes with the whole strong restriction. -/
theorem chartStrongMap_onCharts (f : StrongHom A B)
    (i i' : A.atlas.Index) (j : B.atlas.Index)
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i'))
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (h' : f.baseMap '' Set.range (A.atlas.chart i') ⊆ Set.range (B.atlas.chart j)) :
    A.chartStrongMap i i' hi ≫ f.onCharts i' j h' = f.onCharts i j h := by
  apply toChosen_injective (B.chartTopIndex j) (B.chartTop_contains j)
  refine Hom.ext rfl rfl ?_
  apply heq_of_eq
  funext a
  exact ((A.chartStrongMap i i' hi).compOfTopCharts_pullback_top (f.onCharts i' j h')
    (A.chartTopIndex i') (A.chartTop_contains i') (B.chartTopIndex j)
    (B.chartTop_contains j) a).trans
      (f.restriction_comp_pullback a.val i' j (a.property.trans hi)
        ((Set.image_mono a.property).trans h) h')

/-- Target-domain inclusion commutes with the whole strong restriction. -/
theorem onCharts_chartStrongMap (f : StrongHom A B)
    (i : A.atlas.Index) (j j' : B.atlas.Index)
    (hj : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart j'))
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (h' : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j')) :
    f.onCharts i j h ≫ B.chartStrongMap j j' hj = f.onCharts i j' h' := by
  apply toChosen_injective (B.chartTopIndex j') (B.chartTop_contains j')
  refine Hom.ext rfl rfl ?_
  apply heq_of_eq
  funext a
  exact ((f.onCharts i j h).compOfTopCharts_pullback_top (B.chartStrongMap j j' hj)
    (B.chartTopIndex j) (B.chartTop_contains j) (B.chartTopIndex j')
    (B.chartTop_contains j') a).trans
      (f.pullback_comp_restriction a.val j j' hj
        ((Set.image_mono a.property).trans h)
        ((Set.image_mono a.property).trans h')).symm

end StrongHom

end Langlands.Analytic.AffinoidAtlasPresentation
