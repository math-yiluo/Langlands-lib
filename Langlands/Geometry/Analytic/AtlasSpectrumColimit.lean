import Langlands.Geometry.Analytic.AtlasSpectrumDiagram
import Langlands.Geometry.Analytic.AtlasTopology.Colimit
import Mathlib.CategoryTheory.Limits.IsLimit

/-! # The actual spectrum-chart colimit of a supplied atlas -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory CategoryTheory.Limits Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Index charts and actual members of the range family have the same order. -/
def chartMemberOrderIso :
    ChartObject a ≃o AtlasTopology.Member (Set.range (fun i => Set.range (a.chart i))) where
  toFun i := ⟨Set.range (a.chart i.index), ⟨i.index, rfl⟩⟩
  invFun U := ⟨Classical.choose U.property⟩
  left_inv i := ChartObject.ext (a.chartDomain_injective (Classical.choose_spec
    (show Set.range (a.chart i.index) ∈ Set.range (fun j => Set.range (a.chart j)) from
      ⟨i.index, rfl⟩)))
  right_inv U := Subtype.ext (Classical.choose_spec U.property)
  map_rel_iff' := Iff.rfl

/-- Reindex the actual member-subspace colimit by the chart order equivalence. -/
def chartRangeDiagramCoconeIsColimit : IsColimit a.chartRangeCocone :=
  a.chartRangeCoconeIsColimit.whiskerEquivalence a.chartMemberOrderIso.equivalence

/-- Universe lifting preserves the range cocone's actual universal property. -/
def liftedChartRangeCoconeIsColimit :
    IsColimit (TopCat.uliftFunctor.{u}.mapCocone a.chartRangeCocone) :=
  isColimitOfPreserves TopCat.uliftFunctor.{u} a.chartRangeDiagramCoconeIsColimit

/-- The chart spectrum cocone is exactly the range cocone under comparison. -/
def chartSpectrumCoconeComparison :
    (Cocone.precompose a.chartSpectrumRangeIso.hom).obj
        (TopCat.uliftFunctor.{u}.mapCocone a.chartRangeCocone) ≅
      a.chartSpectrumCocone :=
  Cocone.ext (Iso.refl _) (fun _ => by
    apply TopCat.ext
    intro x
    rfl)

/-- The genuine chart spectra and bounded restriction maps have the lifted
original space as their topological colimit. -/
def chartSpectrumCoconeIsColimit : IsColimit a.chartSpectrumCocone :=
  IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv a.chartSpectrumRangeIso
      (TopCat.uliftFunctor.{u}.mapCocone a.chartRangeCocone)).symm
        a.liftedChartRangeCoconeIsColimit)
    a.chartSpectrumCoconeComparison

/-- The universal continuous map agrees with every supplied spectrum leg. -/
theorem chartSpectrumCocone_desc_chart
    (s : Cocone (a.chartSpectrumDiagram ⋙ TopCat.uliftFunctor.{v}))
    (i : ChartObject a) (x : BanachSpectrum (a.algebra i.index)) :
    a.chartSpectrumCoconeIsColimit.desc s (ULift.up (a.chart i.index x)) =
      s.ι.app i (ULift.up x) :=
  congrArg (fun f : (a.chartSpectrumDiagram ⋙ TopCat.uliftFunctor.{v}).obj i ⟶ s.pt =>
    f (ULift.up x)) (a.chartSpectrumCoconeIsColimit.fac s i)

/-- Values on the actual charts determine a continuous map from the lifted space. -/
theorem chartSpectrumCocone_hom_ext {Y : TopCat.{max u v}}
    {f g : a.chartSpectrumCocone.pt ⟶ Y}
    (h : ∀ (i : ChartObject a) (x : BanachSpectrum (a.algebra i.index)),
      f (ULift.up (a.chart i.index x)) = g (ULift.up (a.chart i.index x))) : f = g := by
  apply a.chartSpectrumCoconeIsColimit.hom_ext
  intro i
  apply TopCat.ext
  intro x
  exact h i x.down

end Langlands.Analytic.IndexedAffinoidAtlas
