import Langlands.Geometry.Analytic.StrongAtlasMaps
import Langlands.Geometry.Analytic.ChosenAtlasRestriction

/-! # Strong maps restricted to arbitrary admissible chart domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- The original continuous map restricted to two actual chart subspaces. -/
def restrictBaseMap (f : StrongHom A B) (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    C(Set.range (A.atlas.chart i), Set.range (B.atlas.chart j)) :=
  ⟨fun x => ⟨f.baseMap x.val, h ⟨x.val, x.property, rfl⟩⟩,
    (f.baseMap.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- Admissibility in the subspace atlases is exactly original admissibility. -/
theorem restrictBaseMap_admissible_iff (f : StrongHom A B)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (c : A.atlas.ContainedChart i) (d : B.atlas.ContainedChart j) :
    (f.restrictBaseMap i j h) '' Set.range ((A.chartPresentation i).atlas.chart c) ⊆
        Set.range ((B.chartPresentation j).atlas.chart d) ↔
      f.baseMap '' Set.range (A.atlas.chart c.val) ⊆ Set.range (B.atlas.chart d.val) := by
  constructor
  · intro hc
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    obtain ⟨y, hy⟩ := hc ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · intro hc
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    obtain ⟨y, hy⟩ := hc ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨y, Subtype.ext hy⟩

/-- Restrict any strong map to any admissible pair of actual chart domains,
retaining every contained chart and every original admissible pullback. -/
def restrictChart (f : StrongHom A B) (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    StrongHom (A.chartPresentation i) (B.chartPresentation j) where
  baseMap := f.restrictBaseMap i j h
  target_exists c := ⟨B.chartTopIndex j,
    (f.restrictBaseMap_admissible_iff i j h c (B.chartTopIndex j)).mpr
      ((Set.image_mono c.property).trans h)⟩
  pullback c d hc := f.pullback c.val d.val
    ((f.restrictBaseMap_admissible_iff i j h c d).mp hc)
  chart_comm c d _hc x := Subtype.ext (f.chart_comm c.val d.val _ x)
  restriction_comm c c' d d' hc hd hcd hc'd' :=
    f.restriction_comm c.val c'.val d.val d'.val
      (A.atlas.chart_subset_of_containedSubset i c c' hc)
      (B.atlas.chart_subset_of_containedSubset j d d' hd)
      ((f.restrictBaseMap_admissible_iff i j h c d).mp hcd)
      ((f.restrictBaseMap_admissible_iff i j h c' d').mp hc'd')

@[simp]
theorem restrictChart_apply_val (f : StrongHom A B)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (x : Set.range (A.atlas.chart i)) :
    ((f.restrictChart i j h).baseMap x).val = f.baseMap x.val := rfl

/-- This is equality of bounded algebra maps, not only equality on spectra. -/
theorem restrictChart_pullback (f : StrongHom A B)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (c : A.atlas.ContainedChart i) (d : B.atlas.ContainedChart j)
    (hc : (f.restrictChart i j h).baseMap ''
      Set.range ((A.chartPresentation i).atlas.chart c) ⊆
        Set.range ((B.chartPresentation j).atlas.chart d)) :
    (f.restrictChart i j h).pullback c d hc =
      f.pullback c.val d.val ((f.restrictBaseMap_admissible_iff i j h c d).mp hc) := rfl

@[simp]
theorem restrictChart_id (i : A.atlas.Index)
    (h : (id A).baseMap '' Set.range (A.atlas.chart i) ⊆
      Set.range (A.atlas.chart i)) :
    (id A).restrictChart i i h = id (A.chartPresentation i) :=
  ext rfl (heq_of_eq (funext fun _ => funext fun _ => funext fun _ => rfl))

/-- At a greatest ambient target chart, restriction agrees with the published
restriction of the associated constant-target chosen map. -/
theorem toChosen_restrictChart (f : StrongHom A B) (t : B.atlas.Index)
    (ht : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart t))
    (i : A.atlas.Index) :
    (f.toChosen t ht).restrictChart i =
      (f.restrictChart i t (f.image_chart_top t ht i)).toChosen
        (B.chartTopIndex t) (B.chartTop_contains t) :=
  Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))

/-- Nested source inclusion commutes with restriction at the fixed greatest
target chart of the actual target-domain presentation. -/
theorem chartMap_restrictChart_toChosen (f : StrongHom A B)
    (i i' : A.atlas.Index) (j : B.atlas.Index)
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i'))
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (h' : f.baseMap '' Set.range (A.atlas.chart i') ⊆ Set.range (B.atlas.chart j)) :
    A.chartMap i i' hi ≫ (f.restrictChart i' j h').toChosen
        (B.chartTopIndex j) (B.chartTop_contains j) =
      (f.restrictChart i j h).toChosen (B.chartTopIndex j) (B.chartTop_contains j) :=
  Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))

/-- The nested-source equality recovers every admissible bounded pullback. -/
theorem restrictChart_source_naturality (f : StrongHom A B)
    (i i' : A.atlas.Index) (j : B.atlas.Index)
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i'))
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (h' : f.baseMap '' Set.range (A.atlas.chart i') ⊆ Set.range (B.atlas.chart j)) :
    ofTopChart
      (A.chartMap i i' hi ≫ (f.restrictChart i' j h').toChosen
        (B.chartTopIndex j) (B.chartTop_contains j))
      (B.chartTopIndex j) (B.chartTop_contains j) = f.restrictChart i j h := by
  rw [chartMap_restrictChart_toChosen f i i' j hi h h']
  exact ofTopChart_toChosen _ _ _

/-- Target inclusion followed by coarsening to the greater target chart
commutes with restriction as equality of chosen bounded maps. -/
theorem restrictChart_toChosen_chartMap (f : StrongHom A B)
    (i : A.atlas.Index) (j j' : B.atlas.Index)
    (hj : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart j'))
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (h' : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j')) :
    (((f.restrictChart i j h).toChosen (B.chartTopIndex j) (B.chartTop_contains j)) ≫
      B.chartMap j j' hj).withTargetChart (B.chartTopIndex j') (B.chartTop_contains j') =
      (f.restrictChart i j' h').toChosen (B.chartTopIndex j') (B.chartTop_contains j') := by
  refine Hom.ext rfl rfl ?_
  apply heq_of_eq
  funext c
  change (f.pullback c.val j _).comp (B.atlas.restriction j j' hj) =
    f.pullback c.val j' _
  exact (f.pullback_comp_restriction c.val j j' hj _ _).symm

/-- The nested-target comparison recovers the complete restricted strong map. -/
theorem restrictChart_target_naturality (f : StrongHom A B)
    (i : A.atlas.Index) (j j' : B.atlas.Index)
    (hj : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart j'))
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (h' : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j')) :
    ofTopChart
      ((((f.restrictChart i j h).toChosen (B.chartTopIndex j) (B.chartTop_contains j)) ≫
        B.chartMap j j' hj).withTargetChart (B.chartTopIndex j') (B.chartTop_contains j'))
      (B.chartTopIndex j') (B.chartTop_contains j') = f.restrictChart i j' h' := by
  rw [restrictChart_toChosen_chartMap f i j j' hj h h']
  exact ofTopChart_toChosen _ _ _

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
