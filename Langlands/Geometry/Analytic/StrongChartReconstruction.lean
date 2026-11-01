import Langlands.Geometry.Analytic.StrongSourceRestriction
import Langlands.Geometry.Analytic.AtlasSpectrumColimit

/-! # Reconstruction from full strong maps on actual source chart domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation

open CategoryTheory CategoryTheory.Limits Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- Full local strong maps, compatible on every original chart containment.
No ambient map or target directedness is part of these data. -/
structure StrongChartMapData (A B : AffinoidAtlasPresentation.{u, v, w} K) where
  localMap : ∀ i, StrongHom (A.chartPresentation i) B
  baseMap_comm : ∀ i i'
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i'))
    (x : Set.range (A.atlas.chart i)),
    (localMap i).baseMap x = (localMap i').baseMap (Set.inclusion hi x)
  pullback_comm : ∀ i i'
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i')) j
    (h : (localMap i).baseMap ''
      Set.range ((A.chartPresentation i).atlas.chart (A.chartTopIndex i)) ⊆
        Set.range (B.atlas.chart j))
    (h' : (localMap i').baseMap ''
      Set.range ((A.chartPresentation i').atlas.chart ⟨i, hi⟩) ⊆
        Set.range (B.atlas.chart j)),
    (localMap i).pullback (A.chartTopIndex i) j h =
      (localMap i').pullback ⟨i, hi⟩ j h'

namespace StrongChartMapData

@[ext]
theorem ext {d e : StrongChartMapData A B} (h : d.localMap = e.localMap) : d = e := by
  cases d
  cases e
  cases h
  rfl

/-- The actual local continuous maps form a cocone on original chart ranges. -/
def chartRangeCocone (d : StrongChartMapData A B) : Cocone A.atlas.chartRangeDiagram where
  pt := B.space
  ι :=
    { app := fun i => TopCat.ofHom (d.localMap i.index).baseMap
      naturality := by
        intro i i' h
        apply TopCat.ext
        intro x
        exact (d.baseMap_comm i.index i'.index (A.atlas.chartSubsetOfHom h) x).symm }

/-- The actual range colimit constructs the global continuous map. -/
def baseMap (d : StrongChartMapData A B) : C(A.space, B.space) :=
  (A.atlas.chartRangeDiagramCoconeIsColimit.desc d.chartRangeCocone).hom

/-- The constructed map agrees with the full local map on its source subspace. -/
@[simp]
theorem baseMap_apply (d : StrongChartMapData A B) (i : A.atlas.Index)
    (x : Set.range (A.atlas.chart i)) :
    d.baseMap x.val = (d.localMap i).baseMap x :=
  congrArg (fun f : A.atlas.chartRangeDiagram.obj ⟨i⟩ ⟶ B.space => f x)
    (A.atlas.chartRangeDiagramCoconeIsColimit.fac d.chartRangeCocone ⟨i⟩)

/-- Global admissibility is exactly admissibility in any containing source chart. -/
theorem admissible_iff (d : StrongChartMapData A B) (i : A.atlas.Index)
    (c : A.atlas.ContainedChart i) (j : B.atlas.Index) :
    d.baseMap '' Set.range (A.atlas.chart c.val) ⊆ Set.range (B.atlas.chart j) ↔
      (d.localMap i).baseMap '' Set.range ((A.chartPresentation i).atlas.chart c) ⊆
        Set.range (B.atlas.chart j) := by
  constructor <;> intro h <;> rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  · exact h ⟨A.atlas.chart c.val x, ⟨x, rfl⟩,
      d.baseMap_apply i ⟨A.atlas.chart c.val x, c.property ⟨x, rfl⟩⟩⟩
  · exact h ⟨(A.chartPresentation i).atlas.chart c x, ⟨x, rfl⟩,
      (d.baseMap_apply i ⟨A.atlas.chart c.val x, c.property ⟨x, rfl⟩⟩).symm⟩

/-- Glue every admissible bounded pullback by taking the whole local source chart. -/
def toStrongHom (d : StrongChartMapData A B) : StrongHom A B where
  baseMap := d.baseMap
  target_exists i := by
    obtain ⟨j, hj⟩ := (d.localMap i).target_exists (A.chartTopIndex i)
    exact ⟨j, (d.admissible_iff i (A.chartTopIndex i) j).mpr hj⟩
  pullback i j h := (d.localMap i).pullback (A.chartTopIndex i) j
    ((d.admissible_iff i (A.chartTopIndex i) j).mp h)
  chart_comm i j h x := by
    exact ((d.localMap i).chart_comm (A.chartTopIndex i) j _ x).trans
      (d.baseMap_apply i _).symm
  restriction_comm i i' j j' hi hj h h' := by
    have hc := (d.admissible_iff i' ⟨i, hi⟩ j).mp h
    have ht := (d.admissible_iff i' (A.chartTopIndex i') j').mp h'
    have hn := (d.localMap i').restriction_comm ⟨i, hi⟩ (A.chartTopIndex i') j j'
      (A.chartTop_contains i' ⟨i, hi⟩) hj hc ht
    change (A.atlas.restriction i i' hi).comp
      ((d.localMap i').pullback (A.chartTopIndex i') j' ht) =
        ((d.localMap i).pullback (A.chartTopIndex i) j
          ((d.admissible_iff i (A.chartTopIndex i) j).mp h)).comp
            (B.atlas.restriction j j' hj)
    rw [d.pullback_comm i i' hi j _ hc]
    exact hn

/-- The construction retains the local bounded map at the whole source chart. -/
theorem toStrongHom_pullback (d : StrongChartMapData A B)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : d.toStrongHom.baseMap '' Set.range (A.atlas.chart i) ⊆
      Set.range (B.atlas.chart j)) :
    d.toStrongHom.pullback i j h =
      (d.localMap i).pullback (A.chartTopIndex i) j
        ((d.admissible_iff i (A.chartTopIndex i) j).mp h) := rfl

end StrongChartMapData

namespace StrongHom

/-- Compare every bounded pullback using separate admissibility witnesses. -/
theorem ext_of_pullback {f g : StrongHom A B} (hb : f.baseMap = g.baseMap)
    (hp : ∀ i j
      (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
      (hg : g.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)),
      f.pullback i j hf = g.pullback i j hg) : f = g := by
  rcases f with ⟨fb, ft, fp, fc, fr⟩
  rcases g with ⟨gb, gt, gp, gc, gr⟩
  dsimp only [baseMap] at hb
  subst gb
  refine StrongHom.ext rfl ?_
  apply heq_of_eq
  funext i j h
  exact hp i j h h

/-- Every global strong map supplies compatible full source-chart restrictions. -/
def toStrongChartMapData (f : StrongHom A B) : StrongChartMapData A B where
  localMap := f.restrictSource
  baseMap_comm _ _ _ _ := rfl
  pullback_comm _ _ _ _ _ _ := rfl

end StrongHom

namespace StrongChartMapData

/-- Recover each entire local strong map, including every bounded subchart map. -/
@[simp]
theorem toStrongHom_restrictSource (d : StrongChartMapData A B) (i : A.atlas.Index) :
    d.toStrongHom.restrictSource i = d.localMap i := by
  refine StrongHom.ext_of_pullback (ContinuousMap.ext (d.baseMap_apply i)) ?_
  intro c j h h'
  exact d.pullback_comm c.val i c.property j _ h'

/-- The glued map is the unique global strong map with the supplied restrictions. -/
theorem toStrongHom_unique (d : StrongChartMapData A B) (f : StrongHom A B)
    (h : ∀ i, f.restrictSource i = d.localMap i) : f = d.toStrongHom := by
  apply StrongHom.ext_of_restrictSource
  intro i
  exact (h i).trans (d.toStrongHom_restrictSource i).symm

/-- Reconstructing and then restricting recovers all full local data. -/
@[simp]
theorem toStrongHom_toStrongChartMapData (d : StrongChartMapData A B) :
    d.toStrongHom.toStrongChartMapData = d := by
  apply StrongChartMapData.ext
  funext i
  exact d.toStrongHom_restrictSource i

end StrongChartMapData

namespace StrongHom

/-- Restriction followed by reconstruction recovers the global strong map in full. -/
@[simp]
theorem toStrongChartMapData_toStrongHom (f : StrongHom A B) :
    f.toStrongChartMapData.toStrongHom = f := by
  apply ext_of_restrictSource
  intro i
  exact f.toStrongChartMapData.toStrongHom_restrictSource i

end StrongHom

namespace StrongChartMapData

/-- Compatible full local maps and global strong maps are equivalent. -/
def strongHomEquiv : StrongChartMapData A B ≃ StrongHom A B where
  toFun := toStrongHom
  invFun := StrongHom.toStrongChartMapData
  left_inv := toStrongHom_toStrongChartMapData
  right_inv := StrongHom.toStrongChartMapData_toStrongHom

end StrongChartMapData

end Langlands.Analytic.AffinoidAtlasPresentation
