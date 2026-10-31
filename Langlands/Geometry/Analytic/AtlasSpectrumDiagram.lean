import Langlands.Geometry.Analytic.ChosenAtlasMorphisms
import Mathlib.Topology.Category.TopCat.ULift
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Whiskering

/-! # The actual affinoid spectrum diagram of a supplied atlas -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory CategoryTheory.Limits Set Topology

namespace IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Chart indices, ordered by containment of their actual ranges. The wrapper
keeps this order local to the supplied atlas. -/
@[ext]
structure ChartObject where
  index : a.Index

instance : PartialOrder (ChartObject a) where
  le i j := Set.range (a.chart i.index) ⊆ Set.range (a.chart j.index)
  le_refl _ := Subset.rfl
  le_trans _ _ _ := Subset.trans
  le_antisymm i j hij hji :=
    ChartObject.ext (a.chartDomain_injective (Subset.antisymm hij hji))

theorem chartSubsetOfHom {i j : ChartObject a} (h : i ⟶ j) :
    Set.range (a.chart i.index) ⊆ Set.range (a.chart j.index) :=
  @leOfHom (ChartObject a) _ i j h

/-- The diagram in the opposite category of genuine affinoid algebras. -/
def chartAffinoidDiagram : ChartObject a ⥤ PresentedAffinoidSpace K where
  obj i := Opposite.op (a.algebra i.index)
  map {i j} h :=
    Quiver.Hom.op (show a.algebra j.index ⟶ a.algebra i.index from
      a.restriction i.index j.index (a.chartSubsetOfHom h))
  map_id i := by
    apply Quiver.Hom.unop_inj
    exact a.restriction_id i.index _
  map_comp {i j k} h g := by
    apply Quiver.Hom.unop_inj
    exact a.restriction_comp i.index j.index k.index _ _ _

/-- The actual spectrum functor applied to the bounded restriction diagram. -/
def chartSpectrumDiagram : ChartObject a ⥤ TopCat.{u} :=
  a.chartAffinoidDiagram ⋙ affinoidSpectrumFunctor K

/-- The range subspaces, with their actual continuous inclusions. -/
def chartRangeDiagram : ChartObject a ⥤ TopCat.{v} where
  obj i := TopCat.of (Set.range (a.chart i.index))
  map h := TopCat.ofHom ⟨Set.inclusion (a.chartSubsetOfHom h),
    continuous_subtype_val.subtype_mk _⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Chart embeddings identify the two lifted objects at a common universe. -/
def chartSpectrumRangeHomeomorph (i : ChartObject a) :
    (a.chartSpectrumDiagram ⋙ TopCat.uliftFunctor.{v}).obj i ≃ₜ
      (a.chartRangeDiagram ⋙ TopCat.uliftFunctor.{u}).obj i :=
  ((a.chartSpectrumDiagram.obj i).uliftFunctorObjHomeo).symm |>.trans
    ((a.isEmbedding_chart i.index).toHomeomorph.trans
      (a.chartRangeDiagram.obj i).uliftFunctorObjHomeo)

@[simp]
theorem chartSpectrumRangeHomeomorph_apply (i : ChartObject a)
    (x : BanachSpectrum (a.algebra i.index)) :
    a.chartSpectrumRangeHomeomorph i (ULift.up x) =
      ULift.up (⟨a.chart i.index x, ⟨x, rfl⟩⟩ :
        Set.range (a.chart i.index)) := rfl

/-- Naturality is the original bounded restriction's chart square. -/
def chartSpectrumRangeIso :
    a.chartSpectrumDiagram ⋙ TopCat.uliftFunctor.{v} ≅
      a.chartRangeDiagram ⋙ TopCat.uliftFunctor.{u} :=
  NatIso.ofComponents (fun i => TopCat.isoOfHomeo (a.chartSpectrumRangeHomeomorph i))
    (by
      intro i j h
      apply TopCat.ext
      intro x
      apply ULift.ext
      apply Subtype.ext
      exact a.restriction_chart i.index j.index (a.chartSubsetOfHom h) x.down)

/-- The usual range-inclusion cocone on the original space. -/
def chartRangeCocone : Cocone a.chartRangeDiagram where
  pt := TopCat.of X
  ι :=
    { app := fun _ => TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
      naturality := fun _ _ _ => rfl }

/-- The actual spectrum charts form a cocone with vertex the lifted space. -/
def chartSpectrumCocone :
    Cocone (a.chartSpectrumDiagram ⋙ TopCat.uliftFunctor.{v}) where
  pt := TopCat.uliftFunctor.{u}.obj (TopCat.of X)
  ι :=
    { app := fun i =>
        TopCat.ofHom ⟨fun x => ULift.up (a.chart i.index x.down),
          continuous_uliftUp.comp
            ((a.isEmbedding_chart i.index).continuous.comp continuous_uliftDown)⟩
      naturality := by
        intro i j h
        apply TopCat.ext
        intro x
        apply ULift.ext
        exact a.restriction_chart i.index j.index (a.chartSubsetOfHom h) x.down }

/-- Comparing spectra with ranges carries their chart cocones to each other. -/
theorem chartSpectrumRangeIso_cocone (i : ChartObject a) :
    (a.chartSpectrumRangeIso.hom.app i) ≫
        (TopCat.uliftFunctor.{u}.mapCocone a.chartRangeCocone).ι.app i =
      a.chartSpectrumCocone.ι.app i := rfl

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation.Hom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K} (f : A ⟶ B)

/-- A monotone chosen chart map gives a functor between the actual chart orders. -/
def chartFunctor :
    IndexedAffinoidAtlas.ChartObject A.atlas ⥤ IndexedAffinoidAtlas.ChartObject B.atlas where
  obj i := ⟨f.indexMap i.index⟩
  map {i j} h := @homOfLE (IndexedAffinoidAtlas.ChartObject B.atlas) _
    ⟨f.indexMap i.index⟩ ⟨f.indexMap j.index⟩
    (f.index_mono _ _ (A.atlas.chartSubsetOfHom h))

/-- The original chosen bounded pullbacks, as an affinoid natural transformation. -/
def chartAffinoidMap :
    A.atlas.chartAffinoidDiagram ⟶ f.chartFunctor ⋙ B.atlas.chartAffinoidDiagram where
  app i := Quiver.Hom.op (show B.atlas.algebra (f.indexMap i.index) ⟶
    A.atlas.algebra i.index from f.pullback i.index)
  naturality i j h := by
    apply Quiver.Hom.unop_inj
    exact f.restriction_comm i.index j.index (A.atlas.chartSubsetOfHom h)

/-- The actual spectral maps of the chosen bounded pullbacks. -/
def chartSpectrumMap :
    A.atlas.chartSpectrumDiagram ⟶ f.chartFunctor ⋙ B.atlas.chartSpectrumDiagram :=
  Functor.whiskerRight f.chartAffinoidMap (affinoidSpectrumFunctor K)

/-- The same continuous map, restricted to the actual source and target ranges. -/
def chartRangeMap :
    A.atlas.chartRangeDiagram ⟶ f.chartFunctor ⋙ B.atlas.chartRangeDiagram where
  app i := TopCat.ofHom ⟨fun x =>
      ⟨f.baseMap x.val, f.image_chart_subset i.index (Set.mem_image_of_mem _ x.property)⟩,
    (f.baseMap.continuous.comp continuous_subtype_val).subtype_mk _⟩
  naturality _ _ _ := rfl

/-- The lifted spectrum/range comparison commutes with the actual chosen map. -/
theorem chartSpectrumRangeIso_naturality
    (i : IndexedAffinoidAtlas.ChartObject A.atlas) :
    TopCat.uliftFunctor.{v}.map (f.chartSpectrumMap.app i) ≫
        B.atlas.chartSpectrumRangeIso.hom.app (f.chartFunctor.obj i) =
      A.atlas.chartSpectrumRangeIso.hom.app i ≫
        TopCat.uliftFunctor.{u}.map (f.chartRangeMap.app i) := by
  apply TopCat.ext
  intro x
  apply ULift.ext
  apply Subtype.ext
  exact f.chart_comm i.index x.down

/-- Chosen maps intertwine the actual lifted spectrum-chart cocones. -/
theorem chartSpectrumCocone_naturality
    (i : IndexedAffinoidAtlas.ChartObject A.atlas) :
    TopCat.uliftFunctor.{v}.map (f.chartSpectrumMap.app i) ≫
        B.atlas.chartSpectrumCocone.ι.app (f.chartFunctor.obj i) =
      A.atlas.chartSpectrumCocone.ι.app i ≫
        TopCat.uliftFunctor.{u}.map (TopCat.ofHom f.baseMap) := by
  apply TopCat.ext
  intro x
  apply ULift.ext
  exact f.chart_comm i.index x.down

end AffinoidAtlasPresentation.Hom

end Langlands.Analytic
