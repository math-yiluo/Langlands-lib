import Langlands.Geometry.Analytic.AtlasRestriction

/-! # Restricting chosen atlas maps to actual chart domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.Hom

open CategoryTheory Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}

/-- Restrict to a source chart domain and its selected target chart domain.
Every contained chart and its actual bounded pullback are retained. -/
def restrictChart (f : A ⟶ B) (i : A.atlas.Index) :
    A.chartPresentation i ⟶ B.chartPresentation (f.indexMap i) where
  baseMap := ⟨fun x => ⟨f.baseMap x.val,
    f.image_chart_subset i ⟨x.val, x.property, rfl⟩⟩,
    (f.baseMap.continuous.comp continuous_subtype_val).subtype_mk _⟩
  indexMap c := ⟨f.indexMap c.val, f.index_mono c.val i c.property⟩
  index_mono c d h := B.atlas.containedChart_subset (f.indexMap i) _ _
    (f.index_mono c.val d.val (A.atlas.chart_subset_of_containedSubset i c d h))
  pullback c := f.pullback c.val
  chart_comm c x := Subtype.ext (f.chart_comm c.val x)
  restriction_comm c d h :=
    f.restriction_comm c.val d.val (A.atlas.chart_subset_of_containedSubset i c d h)

@[simp]
theorem restrictChart_apply_val (f : A ⟶ B) (i : A.atlas.Index)
    (x : Set.range (A.atlas.chart i)) :
    ((f.restrictChart i).baseMap x).val = f.baseMap x.val := rfl

@[simp]
theorem restrictChart_indexMap_val (f : A ⟶ B) (i : A.atlas.Index)
    (c : A.atlas.ContainedChart i) :
    ((f.restrictChart i).indexMap c).val = f.indexMap c.val := rfl

@[simp]
theorem restrictChart_pullback (f : A ⟶ B) (i : A.atlas.Index)
    (c : A.atlas.ContainedChart i) :
    (f.restrictChart i).pullback c = f.pullback c.val := rfl

/-- Restricting commutes with inclusion into the ambient presentations. -/
theorem restrictChart_chartInclusion (f : A ⟶ B) (i : A.atlas.Index) :
    f.restrictChart i ≫ B.chartInclusion (f.indexMap i) = A.chartInclusion i ≫ f :=
  ext rfl rfl (heq_of_eq (funext fun _ => rfl))

@[simp]
theorem restrictChart_id (i : A.atlas.Index) :
    (𝟙 A : A ⟶ A).restrictChart i = 𝟙 (A.chartPresentation i) :=
  ext rfl rfl (heq_of_eq (funext fun _ => rfl))

/-- Composition restricts through the selected intermediate chart. -/
theorem restrictChart_comp (f : A ⟶ B) (g : B ⟶ C) (i : A.atlas.Index) :
    (f ≫ g).restrictChart i =
      f.restrictChart i ≫ g.restrictChart (f.indexMap i) :=
  ext rfl rfl (heq_of_eq (funext fun _ => rfl))

/-- Restriction is compatible with nested source and selected target domains. -/
theorem chartMap_restrictChart (f : A ⟶ B) (i j : A.atlas.Index)
    (hij : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart j)) :
    A.chartMap i j hij ≫ f.restrictChart j =
      f.restrictChart i ≫ B.chartMap (f.indexMap i) (f.indexMap j)
        (f.index_mono i j hij) :=
  ext rfl rfl (heq_of_eq (funext fun _ => rfl))

end Langlands.Analytic.AffinoidAtlasPresentation.Hom
