import Langlands.Geometry.Analytic.StrongAtlasMaps

/-! # Strong atlas composition through greatest charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation

open CategoryTheory Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C D : AffinoidAtlasPresentation.{u, v, w} K}

namespace StrongHom

/-- Restriction naturality with a fixed target is equality of bounded maps. -/
theorem restriction_comp_pullback (f : StrongHom A B) (i i' : A.atlas.Index)
    (j : B.atlas.Index)
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i'))
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (h' : f.baseMap '' Set.range (A.atlas.chart i') ⊆ Set.range (B.atlas.chart j)) :
    (A.atlas.restriction i i' hi).comp (f.pullback i' j h') = f.pullback i j h := by
  simpa only [B.atlas.restriction_id, BoundedAlgHom.comp_id] using
    f.restriction_comm i i' j j hi Subset.rfl h h'

/-- Greatest-target pullbacks detect equality of the entire strong map. -/
theorem toChosen_injective (t : B.atlas.Index)
    (ht : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart t)) :
    Function.Injective (fun f : StrongHom A B => f.toChosen t ht) := by
  intro f g h
  change f.toChosen t ht = g.toChosen t ht at h
  exact (ofTopChart_toChosen f t ht).symm.trans
    ((congrArg (fun k => ofTopChart k t ht) h).trans (ofTopChart_toChosen g t ht))

/-- Compose through supplied greatest intermediate and target charts. All
other admissible pullbacks are constructed by actual domain factorization. -/
def compOfTopCharts (f : StrongHom A B) (g : StrongHom B C)
    (b : B.atlas.Index)
    (hb : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart b))
    (c : C.atlas.Index)
    (hc : ∀ j, Set.range (C.atlas.chart j) ⊆ Set.range (C.atlas.chart c)) :
    StrongHom A C :=
  ofTopChart (f.toChosen b hb ≫ g.toChosen c hc) c hc

@[simp]
theorem compOfTopCharts_baseMap (f : StrongHom A B) (g : StrongHom B C)
    (b : B.atlas.Index)
    (hb : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart b))
    (c : C.atlas.Index)
    (hc : ∀ j, Set.range (C.atlas.chart j) ⊆ Set.range (C.atlas.chart c)) :
    (compOfTopCharts f g b hb c hc).baseMap = g.baseMap.comp f.baseMap := rfl

/-- The chosen map at the greatest target is exactly the chosen composite. -/
theorem compOfTopCharts_toChosen (f : StrongHom A B) (g : StrongHom B C)
    (b : B.atlas.Index)
    (hb : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart b))
    (c : C.atlas.Index)
    (hc : ∀ j, Set.range (C.atlas.chart j) ⊆ Set.range (C.atlas.chart c)) :
    (compOfTopCharts f g b hb c hc).toChosen c hc =
      f.toChosen b hb ≫ g.toChosen c hc := by
  refine Hom.ext rfl rfl ?_
  apply heq_of_eq
  funext i
  exact ofTopChart_pullback_selected (f.toChosen b hb ≫ g.toChosen c hc) c hc i

/-- At any target that contains the image of an intermediate chart, the
composite has exactly the expected composite of bounded pullbacks. -/
theorem compOfTopCharts_pullback (f : StrongHom A B) (g : StrongHom B C)
    (b : B.atlas.Index)
    (hb : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart b))
    (c : C.atlas.Index)
    (hc : ∀ j, Set.range (C.atlas.chart j) ⊆ Set.range (C.atlas.chart c))
    (i : A.atlas.Index) (j : B.atlas.Index) (k : C.atlas.Index)
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hg : g.baseMap '' Set.range (B.atlas.chart j) ⊆ Set.range (C.atlas.chart k))
    (h : (compOfTopCharts f g b hb c hc).baseMap '' Set.range (A.atlas.chart i) ⊆
      Set.range (C.atlas.chart k)) :
    (compOfTopCharts f g b hb c hc).pullback i k h =
      (f.pullback i j hf).comp (g.pullback j k hg) := by
  apply C.atlas.restriction_hom_ext k c (hc k) (A.atlas.algebra i)
  calc
    ((compOfTopCharts f g b hb c hc).pullback i k h).comp
        (C.atlas.restriction k c (hc k)) =
        (f.pullback i b (f.image_chart_top b hb i)).comp
          (g.pullback b c (g.image_chart_top c hc b)) := by
      have hh := ofTopChart_pullback_comp_restriction
        (f.toChosen b hb ≫ g.toChosen c hc) c hc i k h
      change ((compOfTopCharts f g b hb c hc).pullback i k h).comp
        (C.atlas.restriction k c (hc k)) =
          ((f.pullback i b (f.image_chart_top b hb i)).comp
            (g.pullback b c (g.image_chart_top c hc b))).comp
              (C.atlas.restriction c c (hc c)) at hh
      simpa only [C.atlas.restriction_id, BoundedAlgHom.comp_id] using hh
    _ = (f.pullback i j hf).comp (g.pullback j c (g.image_chart_top c hc j)) := by
      rw [f.pullback_comp_restriction i j b (hb j) hf (f.image_chart_top b hb i),
        BoundedAlgHom.comp_assoc,
        g.restriction_comp_pullback j b c (hb j)
          (g.image_chart_top c hc j) (g.image_chart_top c hc b)]
    _ = ((f.pullback i j hf).comp (g.pullback j k hg)).comp
        (C.atlas.restriction k c (hc k)) := by
      rw [BoundedAlgHom.comp_assoc,
        ← g.pullback_comp_restriction j k c (hc k) hg (g.image_chart_top c hc j)]

/-- The strong composite is independent of both greatest chart choices. -/
theorem compOfTopCharts_eq (f : StrongHom A B) (g : StrongHom B C)
    (b b' : B.atlas.Index)
    (hb : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart b))
    (hb' : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart b'))
    (c c' : C.atlas.Index)
    (hc : ∀ j, Set.range (C.atlas.chart j) ⊆ Set.range (C.atlas.chart c))
    (hc' : ∀ j, Set.range (C.atlas.chart j) ⊆ Set.range (C.atlas.chart c')) :
    compOfTopCharts f g b hb c hc = compOfTopCharts f g b' hb' c' hc' := by
  apply toChosen_injective c hc
  dsimp only
  refine Hom.ext rfl rfl ?_
  apply heq_of_eq
  funext i
  exact (compOfTopCharts_pullback f g b hb c hc i b c
    (f.image_chart_top b hb i) (g.image_chart_top c hc b)
      ((compOfTopCharts f g b hb c hc).image_chart_top c hc i)).trans
      (compOfTopCharts_pullback f g b' hb' c' hc' i b c
        (f.image_chart_top b hb i) (g.image_chart_top c hc b)
          ((compOfTopCharts f g b' hb' c' hc').image_chart_top c hc i)).symm

@[simp]
theorem id_compOfTopCharts (f : StrongHom A B)
    (a : A.atlas.Index)
    (ha : ∀ j, Set.range (A.atlas.chart j) ⊆ Set.range (A.atlas.chart a))
    (b : B.atlas.Index)
    (hb : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart b)) :
    compOfTopCharts (id A) f a ha b hb = f := by
  apply toChosen_injective b hb
  dsimp only
  rw [compOfTopCharts_toChosen]
  refine Hom.ext rfl rfl ?_
  apply heq_of_eq
  funext i
  exact f.restriction_comp_pullback i a b (ha i)
    (f.image_chart_top b hb i) (f.image_chart_top b hb a)

@[simp]
theorem compOfTopCharts_id (f : StrongHom A B)
    (b : B.atlas.Index)
    (hb : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart b)) :
    compOfTopCharts f (id B) b hb b hb = f := by
  apply toChosen_injective b hb
  dsimp only
  rw [compOfTopCharts_toChosen]
  refine Hom.ext rfl rfl ?_
  apply heq_of_eq
  funext i
  change (f.pullback i b (f.image_chart_top b hb i)).comp
    (B.atlas.restriction b b Subset.rfl) = f.pullback i b (f.image_chart_top b hb i)
  rw [B.atlas.restriction_id, BoundedAlgHom.comp_id]

/-- Associativity holds for the full family of all admissible pullbacks. -/
theorem compOfTopCharts_assoc (f : StrongHom A B) (g : StrongHom B C)
    (h : StrongHom C D)
    (b : B.atlas.Index)
    (hb : ∀ j, Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart b))
    (c : C.atlas.Index)
    (hc : ∀ j, Set.range (C.atlas.chart j) ⊆ Set.range (C.atlas.chart c))
    (d : D.atlas.Index)
    (hd : ∀ j, Set.range (D.atlas.chart j) ⊆ Set.range (D.atlas.chart d)) :
    compOfTopCharts (compOfTopCharts f g b hb c hc) h c hc d hd =
      compOfTopCharts f (compOfTopCharts g h c hc d hd) b hb d hd := by
  apply toChosen_injective d hd
  dsimp only
  simp only [compOfTopCharts_toChosen, Category.assoc]

end StrongHom

end Langlands.Analytic.AffinoidAtlasPresentation

namespace Langlands.Analytic

open CategoryTheory Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- An actual indexed atlas presentation with one chart containing all its
charts. In particular every chart-domain presentation supplies such an object. -/
structure TopChartPresentation (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] where
  presentation : AffinoidAtlasPresentation.{u, v, w} K
  topChart : presentation.atlas.Index
  top_contains : ∀ j, Set.range (presentation.atlas.chart j) ⊆
    Set.range (presentation.atlas.chart topChart)

namespace TopChartPresentation

/-- The greatest chart covers the actual space, by the atlas net axiom. -/
theorem topChart_surjective (A : TopChartPresentation.{u, v, w} K) :
    Function.Surjective (A.presentation.atlas.chart A.topChart) := by
  intro x
  have hx : x ∈ ⋃₀ Set.range (fun i => Set.range (A.presentation.atlas.chart i)) := by
    rw [A.presentation.atlas.isNet_chartFamily.1.covers]
    trivial
  obtain ⟨U, ⟨i, rfl⟩, hi⟩ := Set.mem_sUnion.mp hx
  exact A.top_contains i hi

/-- The space is homeomorphic to its actual greatest-chart Banach spectrum. -/
def topSpectrumHomeomorph (A : TopChartPresentation.{u, v, w} K) :
    BanachSpectrum (A.presentation.atlas.algebra A.topChart) ≃ₜ A.presentation.space :=
  (A.presentation.atlas.isEmbedding_chart A.topChart).toHomeomorphOfSurjective
    A.topChart_surjective

instance : Category (TopChartPresentation.{u, v, w} K) where
  Hom A B := AffinoidAtlasPresentation.StrongHom A.presentation B.presentation
  id A := AffinoidAtlasPresentation.StrongHom.id A.presentation
  comp {_A B C} f g :=
    f.compOfTopCharts g B.topChart B.top_contains C.topChart C.top_contains
  id_comp {A B} f :=
    f.id_compOfTopCharts A.topChart A.top_contains B.topChart B.top_contains
  comp_id {_A B} f :=
    f.compOfTopCharts_id B.topChart B.top_contains
  assoc {_A B C D} f g h :=
    f.compOfTopCharts_assoc g h B.topChart B.top_contains
      C.topChart C.top_contains D.topChart D.top_contains

@[simp]
theorem baseMap_id (A : TopChartPresentation.{u, v, w} K) :
    (𝟙 A : A ⟶ A).baseMap = ContinuousMap.id A.presentation.space := rfl

@[simp]
theorem baseMap_comp {A B C : TopChartPresentation.{u, v, w} K}
    (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).baseMap = g.baseMap.comp f.baseMap := rfl

/-- The strong-map category retains the actual underlying spaces and maps. -/
def spaceFunctor : TopChartPresentation.{u, v, w} K ⥤ TopCat.{v} where
  obj A := A.presentation.space
  map f := TopCat.ofHom f.baseMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Construct a greatest-chart object from any actual chart-domain subspace,
retaining every original chart contained in that chart. -/
def ofChart (A : AffinoidAtlasPresentation.{u, v, w} K) (i : A.atlas.Index) :
    TopChartPresentation.{u, v, w} K where
  presentation := A.chartPresentation i
  topChart := A.chartTopIndex i
  top_contains := A.chartTop_contains i

end TopChartPresentation

end Langlands.Analytic
