import Langlands.Geometry.Analytic.AtlasTopology.DirectedCompact
import Langlands.Geometry.Analytic.DirectedAtlasComposition
import Langlands.Geometry.Analytic.TopChartAffinoidComparison

/-! # Compact directed atlases and their actual affinoid comparison -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X]
  (a : IndexedAffinoidAtlas.{u, v, w} K X) [Nonempty a.Index]

/-- Compactness and directedness give an original chart covering the whole space. -/
theorem exists_range_eq_univ_of_compactSpace [CompactSpace X]
    (hd : a.HasDirectedCharts) : ∃ i : a.Index, Set.range (a.chart i) = Set.univ := by
  obtain ⟨i, hi⟩ := a.isNet_chartFamily.1.exists_subset_of_isCompact hd
    (isCompact_univ : IsCompact (Set.univ : Set X))
  exact ⟨i, Set.Subset.antisymm (Set.subset_univ _) hi⟩

/-- Original chart domains are indexed injectively, so the whole-space chart is unique. -/
theorem existsUnique_range_eq_univ_of_compactSpace [CompactSpace X]
    (hd : a.HasDirectedCharts) : ∃! i : a.Index, Set.range (a.chart i) = Set.univ := by
  obtain ⟨i, hi⟩ := a.exists_range_eq_univ_of_compactSpace hd
  exact ⟨i, hi, fun j hj => a.chartDomain_injective (hj.trans hi.symm)⟩

/-- In a nonempty directed atlas, compactness is equivalent to an original whole chart. -/
theorem compactSpace_iff_exists_range_eq_univ (hd : a.HasDirectedCharts) :
    CompactSpace X ↔ ∃ i : a.Index, Set.range (a.chart i) = Set.univ := by
  constructor
  · intro h
    let := h
    exact a.exists_range_eq_univ_of_compactSpace hd
  · rintro ⟨i, hi⟩
    exact Function.Surjective.compactSpace (a.isEmbedding_chart i).continuous
      (Set.range_eq_univ.mp hi)

end IndexedAffinoidAtlas

namespace DirectedAtlasPresentation

variable (A : DirectedAtlasPresentation.{u, v, w} K)
  [CompactSpace A.presentation.space] [Nonempty A.presentation.atlas.Index]

/-- Choose the unique whole-space chart, retaining the entire original atlas. -/
def compactTopChart : TopChartPresentation.{u, v, w} K where
  presentation := A.presentation
  topChart := Classical.choose
    (A.presentation.atlas.exists_range_eq_univ_of_compactSpace A.directed)
  top_contains j := by
    rw [Classical.choose_spec
      (A.presentation.atlas.exists_range_eq_univ_of_compactSpace A.directed)]
    exact Set.subset_univ _

@[simp]
theorem compactTopChart_presentation : A.compactTopChart.presentation = A.presentation := rfl

/-- The selected chart is an original chart whose range is exactly the whole space. -/
theorem compactTopChart_range :
    Set.range (A.presentation.atlas.chart A.compactTopChart.topChart) = Set.univ :=
  Set.range_eq_univ.mpr A.compactTopChart.topChart_surjective

/-- Any other original whole-space chart is the selected chart. -/
theorem eq_compactTopChart_of_range_eq_univ (i : A.presentation.atlas.Index)
    (hi : Set.range (A.presentation.atlas.chart i) = Set.univ) :
    i = A.compactTopChart.topChart :=
  A.presentation.atlas.chartDomain_injective (hi.trans A.compactTopChart_range.symm)

/-- The actual compact space is homeomorphic to its original whole-chart spectrum. -/
def compactSpectrumHomeomorph :
    BanachSpectrum (A.presentation.atlas.algebra A.compactTopChart.topChart) ≃ₜ
      A.presentation.space :=
  A.compactTopChart.topSpectrumHomeomorph

/-- Global Hausdorffness follows from this actual spectral homeomorphism. -/
theorem t2Space_of_compactSpace : T2Space A.presentation.space :=
  A.compactSpectrumHomeomorph.t2Space

/-- The actual whole-chart algebra, as a presented affinoid space. -/
def compactAffinoid : PresentedAffinoidSpace K := A.compactTopChart.affinoid

/-- Reinterpreting the same atlas as greatest-chart and directed changes no strong data. -/
def compactTopChartIso : ofTopChart A.compactTopChart ≅ A where
  hom := AffinoidAtlasPresentation.StrongHom.id A.presentation
  inv := AffinoidAtlasPresentation.StrongHom.id A.presentation
  hom_inv_id := by
    change (𝟙 A) ≫ (𝟙 A) = 𝟙 A
    exact Category.id_comp _
  inv_hom_id := by
    change (𝟙 A) ≫ (𝟙 A) = 𝟙 A
    exact Category.id_comp _

variable {A}
  {B C : DirectedAtlasPresentation.{u, v, w} K}
  [CompactSpace B.presentation.space] [Nonempty B.presentation.atlas.Index]
  [CompactSpace C.presentation.space] [Nonempty C.presentation.atlas.Index]

/-- Retain the actual bounded pullback on the unique whole-space charts. -/
def compactPullback (f : A ⟶ B) :
    BoundedAlgHom K (B.presentation.atlas.algebra B.compactTopChart.topChart)
      (A.presentation.atlas.algebra A.compactTopChart.topChart) :=
  TopChartPresentation.topPullback (A := A.compactTopChart) (B := B.compactTopChart) f

@[simp]
theorem compactPullback_id :
    compactPullback (𝟙 A) =
      BoundedAlgHom.id K (A.presentation.atlas.algebra A.compactTopChart.topChart) :=
  TopChartPresentation.topPullback_id A.compactTopChart

/-- Directed strong composition corresponds to contravariant bounded composition. -/
theorem compactPullback_comp (f : A ⟶ B) (g : B ⟶ C) :
    compactPullback (f ≫ g) = (compactPullback f).comp (compactPullback g) := by
  exact (congrArg (TopChartPresentation.topPullback
    (A := A.compactTopChart) (B := C.compactTopChart))
    (f.compOfDirected_eq_compOfTopCharts g B.directed C.directed
      B.compactTopChart.topChart B.compactTopChart.top_contains
      C.compactTopChart.topChart C.compactTopChart.top_contains)).trans
        (TopChartPresentation.topPullback_comp
          (A := A.compactTopChart) (B := B.compactTopChart) (C := C.compactTopChart) f g)

/-- Every bounded whole-chart map constructs exactly one full strong morphism.
This retains algebra data, including on nonreduced algebras. -/
def compactPullbackEquiv (A B : DirectedAtlasPresentation.{u, v, w} K)
    [CompactSpace A.presentation.space] [Nonempty A.presentation.atlas.Index]
    [CompactSpace B.presentation.space] [Nonempty B.presentation.atlas.Index] :
    (A ⟶ B) ≃ BoundedAlgHom K (B.presentation.atlas.algebra B.compactTopChart.topChart)
      (A.presentation.atlas.algebra A.compactTopChart.topChart) :=
  TopChartPresentation.topPullbackEquiv A.compactTopChart B.compactTopChart

/-- The inverse constructs the actual restriction followed by the supplied bounded map. -/
theorem compactPullbackEquiv_symm_pullback_top
    (φ : BoundedAlgHom K (B.presentation.atlas.algebra B.compactTopChart.topChart)
      (A.presentation.atlas.algebra A.compactTopChart.topChart))
    (i : A.presentation.atlas.Index)
    (h : ((compactPullbackEquiv A B).symm φ).baseMap '' Set.range (A.presentation.atlas.chart i) ⊆
      Set.range (B.presentation.atlas.chart B.compactTopChart.topChart)) :
    ((compactPullbackEquiv A B).symm φ).pullback i B.compactTopChart.topChart h =
      (A.presentation.atlas.restriction i A.compactTopChart.topChart
        (A.compactTopChart.top_contains i)).comp φ :=
  TopChartPresentation.ofTopPullback_pullback_top
    (A := A.compactTopChart) (B := B.compactTopChart) φ i h

/-- All admissible local pullbacks are the actual bounded domain factorizations. -/
theorem compactPullbackEquiv_symm_comp_restriction
    (φ : BoundedAlgHom K (B.presentation.atlas.algebra B.compactTopChart.topChart)
      (A.presentation.atlas.algebra A.compactTopChart.topChart))
    (i : A.presentation.atlas.Index) (j : B.presentation.atlas.Index)
    (h : ((compactPullbackEquiv A B).symm φ).baseMap '' Set.range (A.presentation.atlas.chart i) ⊆
      Set.range (B.presentation.atlas.chart j)) :
    (((compactPullbackEquiv A B).symm φ).pullback i j h).comp
        (B.presentation.atlas.restriction j B.compactTopChart.topChart
          (B.compactTopChart.top_contains j)) =
      (A.presentation.atlas.restriction i A.compactTopChart.topChart
        (A.compactTopChart.top_contains i)).comp φ :=
  TopChartPresentation.ofTopPullback_comp_restriction
    (A := A.compactTopChart) (B := B.compactTopChart) φ i j h

/-- The actual point map is the spectrum comap in the unique whole-chart coordinates. -/
theorem compactSpectrumHomeomorph_naturality (f : A ⟶ B)
    (x : BanachSpectrum (A.presentation.atlas.algebra A.compactTopChart.topChart)) :
    B.compactSpectrumHomeomorph (BanachSpectrum.comap (compactPullback f).toBoundedRingHom x) =
      f.baseMap (A.compactSpectrumHomeomorph x) :=
  TopChartPresentation.topSpectrumHomeomorph_naturality
    (A := A.compactTopChart) (B := B.compactTopChart) f x

end DirectedAtlasPresentation

namespace DirectedAtlasPresentation

/-- The compact directed presentation is strongly isomorphic to its actual singleton affinoid.
The universes are those of the published singleton realization. -/
def compactAffinoidIso (A : DirectedAtlasPresentation.{u, u, 0} K)
    [CompactSpace A.presentation.space] [Nonempty A.presentation.atlas.Index] :
    ofTopChart (TopChartPresentation.ofAffinoid A.compactAffinoid) ≅ A :=
  (topChartFunctor.mapIso A.compactTopChart.singletonComparisonIso) ≪≫ A.compactTopChartIso

@[simp]
theorem compactAffinoidIso_hom (A : DirectedAtlasPresentation.{u, u, 0} K)
    [CompactSpace A.presentation.space] [Nonempty A.presentation.atlas.Index] :
    A.compactAffinoidIso.hom = A.compactTopChart.singletonComparisonIso.hom := by
  exact A.compactTopChart.singletonComparisonIso.hom.compOfDirected_id A.directed

@[simp]
theorem compactAffinoidIso_inv (A : DirectedAtlasPresentation.{u, u, 0} K)
    [CompactSpace A.presentation.space] [Nonempty A.presentation.atlas.Index] :
    A.compactAffinoidIso.inv = A.compactTopChart.singletonComparisonIso.inv := by
  exact A.compactTopChart.singletonComparisonIso.inv.id_compOfDirected A.directed
    (ofTopChart (TopChartPresentation.ofAffinoid A.compactAffinoid)).directed

end DirectedAtlasPresentation

end Langlands.Analytic
