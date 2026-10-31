import Langlands.Geometry.Analytic.AtlasSpectrumColimit

/-! # Reconstructing chosen atlas maps from bounded chart pullbacks -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation

open CategoryTheory CategoryTheory.Limits Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Local bounded data with monotone target choices. No ambient map is input. -/
structure ChartMapData (A B : AffinoidAtlasPresentation.{u, v, w} K) where
  indexMap : A.atlas.Index → B.atlas.Index
  index_mono : ∀ i j, Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart j) →
    Set.range (B.atlas.chart (indexMap i)) ⊆ Set.range (B.atlas.chart (indexMap j))
  pullback : ∀ i, BoundedAlgHom K (B.atlas.algebra (indexMap i)) (A.atlas.algebra i)
  restriction_comm : ∀ i j h,
    (A.atlas.restriction i j h).comp (pullback j) =
      (pullback i).comp (B.atlas.restriction (indexMap i) (indexMap j) (index_mono i j h))

namespace ChartMapData

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

@[ext]
theorem ext {d e : ChartMapData A B} (hi : d.indexMap = e.indexMap)
    (hp : HEq d.pullback e.pullback) : d = e := by
  cases d
  cases e
  cases hi
  cases eq_of_heq hp
  rfl

/-- The monotone chart choices define a functor on actual chart containments. -/
def chartFunctor (d : ChartMapData A B) :
    IndexedAffinoidAtlas.ChartObject A.atlas ⥤ IndexedAffinoidAtlas.ChartObject B.atlas where
  obj i := ⟨d.indexMap i.index⟩
  map {i j} h := @homOfLE (IndexedAffinoidAtlas.ChartObject B.atlas) _
    ⟨d.indexMap i.index⟩ ⟨d.indexMap j.index⟩
    (d.index_mono _ _ (A.atlas.chartSubsetOfHom h))

/-- The supplied bounded pullbacks form an actual affinoid natural transformation. -/
def chartAffinoidMap (d : ChartMapData A B) :
    A.atlas.chartAffinoidDiagram ⟶ d.chartFunctor ⋙ B.atlas.chartAffinoidDiagram where
  app i := Quiver.Hom.op (show B.atlas.algebra (d.indexMap i.index) ⟶
    A.atlas.algebra i.index from d.pullback i.index)
  naturality i j h := by
    apply Quiver.Hom.unop_inj
    exact d.restriction_comm i.index j.index (A.atlas.chartSubsetOfHom h)

/-- Apply the genuine spectrum functor to the bounded local maps. -/
def chartSpectrumMap (d : ChartMapData A B) :
    A.atlas.chartSpectrumDiagram ⟶ d.chartFunctor ⋙ B.atlas.chartSpectrumDiagram :=
  Functor.whiskerRight d.chartAffinoidMap (affinoidSpectrumFunctor K)

/-- The local spectrum maps followed by target chart embeddings form a cocone. -/
def chartCocone (d : ChartMapData A B) :
    Cocone (A.atlas.chartSpectrumDiagram ⋙ TopCat.uliftFunctor.{v}) where
  pt := B.atlas.chartSpectrumCocone.pt
  ι := Functor.whiskerRight d.chartSpectrumMap TopCat.uliftFunctor.{v} ≫
    Functor.whiskerLeft d.chartFunctor B.atlas.chartSpectrumCocone.ι

/-- The spectrum-chart colimit constructs the continuous map of lifted spaces. -/
def liftedBaseMap (d : ChartMapData A B) :
    A.atlas.chartSpectrumCocone.pt ⟶ B.atlas.chartSpectrumCocone.pt :=
  A.atlas.chartSpectrumCoconeIsColimit.desc d.chartCocone

/-- Remove the explicit universe lifts from the constructed continuous map. -/
def baseMap (d : ChartMapData A B) : C(A.space, B.space) :=
  ⟨fun x => (d.liftedBaseMap (ULift.up x)).down,
    continuous_uliftDown.comp
      (d.liftedBaseMap.hom.continuous.comp continuous_uliftUp)⟩

/-- The constructed ambient map has precisely the supplied chart formula. -/
theorem chart_comm (d : ChartMapData A B) (i : A.atlas.Index)
    (x : BanachSpectrum (A.atlas.algebra i)) :
    B.atlas.chart (d.indexMap i) (BanachSpectrum.comap (d.pullback i).toBoundedRingHom x) =
      d.baseMap (A.atlas.chart i x) :=
  (congrArg ULift.down
    (A.atlas.chartSpectrumCocone_desc_chart d.chartCocone ⟨i⟩ x)).symm

/-- The chart formula determines the ambient continuous map uniquely. -/
theorem baseMap_unique (d : ChartMapData A B) (g : C(A.space, B.space))
    (hg : ∀ i (x : BanachSpectrum (A.atlas.algebra i)),
      B.atlas.chart (d.indexMap i) (BanachSpectrum.comap (d.pullback i).toBoundedRingHom x) =
        g (A.atlas.chart i x)) :
    d.baseMap = g := by
  have h : d.liftedBaseMap = TopCat.uliftFunctor.{u}.map (TopCat.ofHom g) := by
    apply A.atlas.chartSpectrumCocone_hom_ext
    intro i x
    exact (A.atlas.chartSpectrumCocone_desc_chart d.chartCocone i x).trans
      (congrArg ULift.up (hg i.index x))
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun f : A.atlas.chartSpectrumCocone.pt ⟶
    B.atlas.chartSpectrumCocone.pt => (f (ULift.up x)).down) h

/-- Construct a chosen atlas arrow, retaining all original bounded pullbacks. -/
def toHom (d : ChartMapData A B) : A ⟶ B where
  baseMap := d.baseMap
  indexMap := d.indexMap
  index_mono := d.index_mono
  pullback := d.pullback
  chart_comm := d.chart_comm
  restriction_comm := d.restriction_comm

@[simp]
theorem toHom_indexMap (d : ChartMapData A B) : d.toHom.indexMap = d.indexMap := rfl

@[simp]
theorem toHom_pullback (d : ChartMapData A B) (i : A.atlas.Index) :
    d.toHom.pullback i = d.pullback i := rfl

end ChartMapData

namespace Hom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- Forget the ambient map and chart formulas, retaining the actual bounded data. -/
def toChartMapData (f : A ⟶ B) : ChartMapData A B where
  indexMap := f.indexMap
  index_mono := f.index_mono
  pullback := f.pullback
  restriction_comm := f.restriction_comm

@[simp]
theorem toChartMapData_baseMap (f : A ⟶ B) : f.toChartMapData.baseMap = f.baseMap :=
  f.toChartMapData.baseMap_unique f.baseMap f.chart_comm

/-- Reconstructing an existing arrow recovers both its ambient and bounded maps. -/
@[simp]
theorem toChartMapData_toHom (f : A ⟶ B) : f.toChartMapData.toHom = f :=
  Hom.ext f.toChartMapData_baseMap rfl (heq_of_eq rfl)

end Hom

namespace ChartMapData

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

@[simp]
theorem toHom_toChartMapData (d : ChartMapData A B) : d.toHom.toChartMapData = d := rfl

/-- Compatible bounded local data are equivalent to chosen atlas morphisms. -/
def homEquiv : ChartMapData A B ≃ (A ⟶ B) where
  toFun := toHom
  invFun := Hom.toChartMapData
  left_inv := toHom_toChartMapData
  right_inv := Hom.toChartMapData_toHom

end ChartMapData

end Langlands.Analytic.AffinoidAtlasPresentation
