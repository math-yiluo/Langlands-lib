import Langlands.Geometry.Analytic.RationalCutComparison
import Langlands.Geometry.Analytic.DirectedAtlasComposition

/-! # Actual categorical isomorphisms for rational-cut atlases -/

noncomputable section

universe u v w

namespace Langlands.Analytic.RationalCutAtlas

open CategoryTheory Set PresentedAffinoidAlgebra AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X]
  (a : IndexedAffinoidAtlas.{u, v, w} K X) (t : a.Index)
  (ht : ∀ i, Set.range (a.chart i) ⊆ Set.range (a.chart t))

/-- The old-to-cut-to-old composite is the full original bounded restriction. -/
theorem fromOriginalInclusion_comp_toOriginalInclusion
    (i : a.Index) (s : Index a t) (j : a.Index)
    (hf : Set.range (a.chart i) ⊆ Set.range (chart a t ht s))
    (hg : Set.range (chart a t ht s) ⊆ Set.range (a.chart j))
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j)) :
    (fromOriginalInclusion a t ht i s hf).restriction.comp
        (toOriginalInclusion a t ht s j hg).restriction =
      a.restriction i j h :=
  congrArg Domain.Inclusion.restriction
    (@Subsingleton.elim (Domain.Inclusion (a.restrictionDomain i t (ht i))
      (a.restrictionDomain j t (ht j))) inferInstance
      (fromOriginalInclusion a t ht i s hf ≫ toOriginalInclusion a t ht s j hg)
      (originalInclusion a t ht i j h))

/-- The cut-to-old-to-cut composite is the full constructed cut restriction. -/
theorem toOriginalInclusion_comp_fromOriginalInclusion
    (s : Index a t) (i : a.Index) (r : Index a t)
    (hf : Set.range (chart a t ht s) ⊆ Set.range (a.chart i))
    (hg : Set.range (a.chart i) ⊆ Set.range (chart a t ht r))
    (h : Set.range (chart a t ht s) ⊆ Set.range (chart a t ht r)) :
    (toOriginalInclusion a t ht s i hf).restriction.comp
        (fromOriginalInclusion a t ht i r hg).restriction =
      restriction a t ht s r h :=
  congrArg Domain.Inclusion.restriction
    (@Subsingleton.elim (Domain.Inclusion (s.domain a t ht)
      (r.domain a t ht)) inferInstance
      (toOriginalInclusion a t ht s i hf ≫ fromOriginalInclusion a t ht i r hg)
      (inclusion a t ht s r h))

/-- The actual lifted original atlas has the given greatest original chart. -/
def originalTopPresentation : TopChartPresentation.{u, v, max v w} K where
  presentation := originalPresentation a
  topChart := ULift.up t
  top_contains i := ht i.down

/-- The retained greatest original locus is greatest among all actual cuts. -/
theorem presentation_top_contains (s : (presentation a t ht).atlas.Index) :
    Set.range ((presentation a t ht).atlas.chart s) ⊆
      Set.range ((presentation a t ht).atlas.chart
        (ULift.up (Index.ofOriginal a t t))) := by
  change Set.range ((atlas a t ht).chart s.down) ⊆
    Set.range ((atlas a t ht).chart (Index.ofOriginal a t t))
  rw [atlas_ofOriginal_range]
  intro x _
  exact greatest_chart_surjective a t ht x

/-- The actual cut atlas is an object of the existing greatest-chart category. -/
def topPresentation : TopChartPresentation.{u, v, max v w} K where
  presentation := presentation a t ht
  topChart := ULift.up (Index.ofOriginal a t t)
  top_contains := presentation_top_contains a t ht

/-- The old presentation, retaining its actual algebra maps, is directed. -/
def originalDirectedPresentation : DirectedAtlasPresentation.{u, v, max v w} K :=
  DirectedAtlasPresentation.ofTopChart (originalTopPresentation a t ht)

/-- The cut presentation is directed through its proved greatest cut. -/
def directedPresentation : DirectedAtlasPresentation.{u, v, max v w} K :=
  DirectedAtlasPresentation.ofTopChart (topPresentation a t ht)

/-- Directed composition of the forward and reverse full comparisons is
the entire original identity strong morphism. -/
theorem fromOriginal_comp_toOriginal :
    (fromOriginal a t ht).compOfDirected (toOriginal a t ht)
        (directedPresentation a t ht).directed
        (originalDirectedPresentation a t ht).directed =
      StrongHom.id (originalPresentation a) := by
  refine StrongHom.ext_of_directed
    (originalDirectedPresentation a t ht).directed rfl ?_
  intro i
  let s : (presentation a t ht).atlas.Index := ULift.up (Index.ofOriginal a t t)
  let j : (originalPresentation a).atlas.Index := ULift.up t
  have hf := (fromOriginal a t ht).image_chart_top s
    (topPresentation a t ht).top_contains i
  have hg := (toOriginal a t ht).image_chart_top j
    (originalTopPresentation a t ht).top_contains s
  have h := (fromOriginal a t ht).comp_admissible (toOriginal a t ht) i s j hf hg
  refine ⟨j, h, ?_⟩
  rw [StrongHom.compOfDirected_pullback (fromOriginal a t ht) (toOriginal a t ht)
    (directedPresentation a t ht).directed
    (originalDirectedPresentation a t ht).directed i s j hf hg h]
  exact fromOriginalInclusion_comp_toOriginalInclusion a t ht i.down s.down j.down
    (fun x hx => hf ⟨x, hx, rfl⟩) (fun x hx => hg ⟨x, hx, rfl⟩)
    (fun x hx => h ⟨x, hx, rfl⟩)

/-- Directed composition in the reverse order is the entire cut identity,
including every admissible bounded pullback. -/
theorem toOriginal_comp_fromOriginal :
    (toOriginal a t ht).compOfDirected (fromOriginal a t ht)
        (originalDirectedPresentation a t ht).directed
        (directedPresentation a t ht).directed =
      StrongHom.id (presentation a t ht) := by
  refine StrongHom.ext_of_directed (directedPresentation a t ht).directed rfl ?_
  intro s
  let i : (originalPresentation a).atlas.Index := ULift.up t
  let r : (presentation a t ht).atlas.Index := ULift.up (Index.ofOriginal a t t)
  have hf := (toOriginal a t ht).image_chart_top i
    (originalTopPresentation a t ht).top_contains s
  have hg := (fromOriginal a t ht).image_chart_top r
    (topPresentation a t ht).top_contains i
  have h := (toOriginal a t ht).comp_admissible (fromOriginal a t ht) s i r hf hg
  refine ⟨r, h, ?_⟩
  rw [StrongHom.compOfDirected_pullback (toOriginal a t ht) (fromOriginal a t ht)
    (originalDirectedPresentation a t ht).directed
    (directedPresentation a t ht).directed s i r hf hg h]
  exact toOriginalInclusion_comp_fromOriginalInclusion a t ht s.down i.down r.down
    (fun x hx => hf ⟨x, hx, rfl⟩) (fun x hx => hg ⟨x, hx, rfl⟩)
    (fun x hx => h ⟨x, hx, rfl⟩)

/-- The forward round trip also uses exactly the original greatest-chart
composition, with equality of the full strong maps. -/
theorem fromOriginal_comp_toOriginal_top :
    (fromOriginal a t ht).compOfTopCharts (toOriginal a t ht)
        (topPresentation a t ht).topChart (topPresentation a t ht).top_contains
        (originalTopPresentation a t ht).topChart
        (originalTopPresentation a t ht).top_contains =
      StrongHom.id (originalPresentation a) :=
  ((fromOriginal a t ht).compOfDirected_eq_compOfTopCharts (toOriginal a t ht)
    (directedPresentation a t ht).directed
    (originalDirectedPresentation a t ht).directed
    (topPresentation a t ht).topChart (topPresentation a t ht).top_contains
    (originalTopPresentation a t ht).topChart
    (originalTopPresentation a t ht).top_contains).symm.trans
      (fromOriginal_comp_toOriginal a t ht)

/-- The reverse round trip is likewise the full greatest-chart identity. -/
theorem toOriginal_comp_fromOriginal_top :
    (toOriginal a t ht).compOfTopCharts (fromOriginal a t ht)
        (originalTopPresentation a t ht).topChart
        (originalTopPresentation a t ht).top_contains
        (topPresentation a t ht).topChart (topPresentation a t ht).top_contains =
      StrongHom.id (presentation a t ht) :=
  ((toOriginal a t ht).compOfDirected_eq_compOfTopCharts (fromOriginal a t ht)
    (originalDirectedPresentation a t ht).directed
    (directedPresentation a t ht).directed
    (originalTopPresentation a t ht).topChart
    (originalTopPresentation a t ht).top_contains
    (topPresentation a t ht).topChart
    (topPresentation a t ht).top_contains).symm.trans
      (toOriginal_comp_fromOriginal a t ht)

/-- An actual isomorphism of greatest-chart presentations, with the
constructed full comparison maps as its two arrows. -/
def topIso : originalTopPresentation a t ht ≅ topPresentation a t ht where
  hom := fromOriginal a t ht
  inv := toOriginal a t ht
  hom_inv_id := fromOriginal_comp_toOriginal_top a t ht
  inv_hom_id := toOriginal_comp_fromOriginal_top a t ht

/-- The same actual comparison is an isomorphism for directed composition. -/
def directedIso :
    originalDirectedPresentation a t ht ≅ directedPresentation a t ht where
  hom := fromOriginal a t ht
  inv := toOriginal a t ht
  hom_inv_id := fromOriginal_comp_toOriginal a t ht
  inv_hom_id := toOriginal_comp_fromOriginal a t ht

@[simp]
theorem topIso_hom : (topIso a t ht).hom = fromOriginal a t ht := rfl

@[simp]
theorem topIso_inv : (topIso a t ht).inv = toOriginal a t ht := rfl

@[simp]
theorem directedIso_hom : (directedIso a t ht).hom = fromOriginal a t ht := rfl

@[simp]
theorem directedIso_inv : (directedIso a t ht).inv = toOriginal a t ht := rfl

/-- The fully faithful greatest-chart embedding preserves this exact
isomorphism, including its complete comparison arrows. -/
theorem directedIso_eq_mapIso_topIso :
    directedIso a t ht =
      DirectedAtlasPresentation.topChartFunctor.mapIso (topIso a t ht) := by
  apply CategoryTheory.Iso.ext
  rfl

end Langlands.Analytic.RationalCutAtlas
