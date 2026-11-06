import Langlands.Geometry.Analytic.SubatlasDomainAffinoidRealization
import Langlands.Geometry.Analytic.RecognizedOriginalDomains
import Langlands.Geometry.Analytic.RecognizedAffinoidAtlas

/-! # Finite selected-chart refinements of arbitrary recognized subsets -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)
  {P : a.Index → Prop} (hP : a.IsLocallyRefiningSelection P)
  (V : a.saturatedAtlas.RecognizedSubset)

/-- Each original component has its actual old local-domain presentation. -/
def subatlasRecognitionLocalParent (i : Fin V.property.cover.size) :
    LocalDomain a :=
  a.saturatedRepresentative (V.property.cover.index i)

/-- Construct a finite selected-saturation cover of each actual old component. -/
def subatlasRecognitionInnerGluing (i : Fin V.property.cover.size) :
    FiniteChartGluingData (a.subatlas P hP).saturatedAtlas :=
  (a.selectedChartCover P hP (a.subatlasRecognitionLocalParent V i).index).saturatedDomainGluing
    hP (a.subatlasRecognitionLocalParent V i).domain

/-- This inner realization has exactly the algebra of the outer component
as parent, with all full bounded component maps constructed. -/
def subatlasRecognitionInnerRealization (i : Fin V.property.cover.size) :
    (a.subatlasRecognitionInnerGluing hP V i).AffinoidRealization :=
  (a.selectedChartCover P hP (a.subatlasRecognitionLocalParent V i).index).saturatedDomainAffinoidRealization
    hP (a.subatlasRecognitionLocalParent V i).domain

/-- The finite dependent family of outer and inner component indices. -/
abbrev SubatlasRecognitionComponentIndex :=
  (i : Fin V.property.cover.size) × Fin (a.subatlasRecognitionInnerGluing hP V i).size

/-- Extend each inner full domain through the actual outer component,
retaining its selected-saturation algebra and both structural maps. -/
def subatlasRecognitionComponent (t : a.SubatlasRecognitionComponentIndex hP V) :
    Domain K V.algebra :=
  (V.property.componentDomain t.1).extend
    ((a.subatlasRecognitionInnerRealization hP V t.1).domainCover.obj t.2)

@[simp]
theorem subatlasRecognitionComponent_algebra (t : a.SubatlasRecognitionComponentIndex hP V) :
    (a.subatlasRecognitionComponent hP V t).algebra =
      (a.subatlas P hP).saturatedAtlas.algebra ((a.subatlasRecognitionInnerGluing hP V t.1).index t.2) := rfl

/-- The unchanged bounded structural map is the full composite through
the actual outer component algebra. -/
theorem subatlasRecognitionComponent_baseMap (t : a.SubatlasRecognitionComponentIndex hP V) :
    (a.subatlasRecognitionComponent hP V t).baseMap =
      ((a.subatlasRecognitionInnerRealization hP V t.1).restriction t.2).comp
        (V.property.componentDomain t.1).baseMap := rfl

/-- The extended component recovers its selected-saturation chart
under the unchanged original recognized chart. -/
theorem subatlasRecognitionComponent_over_ambient
    (t : a.SubatlasRecognitionComponentIndex hP V)
    (x : BanachSpectrum
      ((a.subatlas P hP).saturatedAtlas.algebra ((a.subatlasRecognitionInnerGluing hP V t.1).index t.2))) :
    V.chart ((a.subatlasRecognitionComponent hP V t).spectrumMap x) =
      (a.subatlas P hP).saturatedAtlas.chart ((a.subatlasRecognitionInnerGluing hP V t.1).index t.2) x := by
  let C := V.property.componentDomain t.1
  let I := (a.subatlasRecognitionInnerRealization hP V t.1).domainCover.obj t.2
  have hs : (C.extend I).spectrumMap x = C.spectrumMap (I.spectrumMap x) :=
    BanachSpectrum.ext fun _ => rfl
  exact (congrArg V.chart hs).trans
    ((V.property.componentDomain_over_ambient t.1 (I.spectrumMap x)).trans
      ((a.subatlasRecognitionInnerRealization hP V t.1).restriction_chart t.2 x))

/-- Each full component has the precise inverse-image locus of its
selected-saturation chart range. -/
theorem subatlasRecognitionComponent_locus (t : a.SubatlasRecognitionComponentIndex hP V) :
    (a.subatlasRecognitionComponent hP V t).locus =
      V.chart ⁻¹' Set.range
        ((a.subatlas P hP).saturatedAtlas.chart ((a.subatlasRecognitionInnerGluing hP V t.1).index t.2)) := by
  let R := a.subatlasRecognitionComponent hP V t
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := R.represents.2.1.symm ▸ hx
    exact ⟨y, (a.subatlasRecognitionComponent_over_ambient hP V t y).symm.trans
      (congrArg V.chart hy)⟩
  · rintro ⟨y, hy⟩
    have h : R.spectrumMap y = x :=
      V.isEmbedding_chart.injective
        ((a.subatlasRecognitionComponent_over_ambient hP V t y).trans hy)
    exact h ▸ R.represents.hasImageIn y

/-- Reindex the actual finite dependent family by a finite ordinal. -/
def subatlasRecognitionComponentEnumeration :
    Fin (Fintype.card (a.SubatlasRecognitionComponentIndex hP V)) ≃
      a.SubatlasRecognitionComponentIndex hP V :=
  (Fintype.equivFin (a.SubatlasRecognitionComponentIndex hP V)).symm

/-- Every point is covered by an actual selected-saturation full domain.
Coverage is proved by the two successive full-domain covers. -/
def subatlasRecognitionDomainCover :
    Domain.FiniteCover (Domain.whole K V.algebra) where
  size := Fintype.card (a.SubatlasRecognitionComponentIndex hP V)
  obj k := a.subatlasRecognitionComponent hP V (a.subatlasRecognitionComponentEnumeration hP V k)
  map k := ⟨(a.subatlasRecognitionComponent hP V
    (a.subatlasRecognitionComponentEnumeration hP V k)).baseMap, rfl⟩
  covers x _ := by
    obtain ⟨i, hi⟩ := V.componentCover.covers x (Set.mem_univ x)
    have hi' : x ∈ (V.property.componentDomain i).locus := hi
    obtain ⟨y, hy⟩ := (V.property.componentDomain i).represents.2.1.symm ▸ hi'
    obtain ⟨j, hj⟩ :=
      (a.subatlasRecognitionInnerRealization hP V i).domainCover.covers y (Set.mem_univ y)
    let t : a.SubatlasRecognitionComponentIndex hP V := ⟨i, j⟩
    refine ⟨(a.subatlasRecognitionComponentEnumeration hP V).symm t, ?_⟩
    rw [Equiv.apply_symm_apply]
    exact ⟨y, hj, hy⟩

/-- The retained selected-saturation chart index of each flattened component. -/
def subatlasRecognitionChartIndex
    (k : Fin (a.subatlasRecognitionDomainCover hP V).size) : (a.subatlas P hP).saturatedAtlas.Index :=
  let t := a.subatlasRecognitionComponentEnumeration hP V k
  (a.subatlasRecognitionInnerGluing hP V t.1).index t.2

@[simp]
theorem subatlasRecognitionDomainCover_obj_algebra
    (k : Fin (a.subatlasRecognitionDomainCover hP V).size) :
    ((a.subatlasRecognitionDomainCover hP V).obj k).algebra =
      (a.subatlas P hP).saturatedAtlas.algebra (a.subatlasRecognitionChartIndex hP V k) := rfl

theorem subatlasRecognitionDomainCover_over_ambient
    (k : Fin (a.subatlasRecognitionDomainCover hP V).size)
    (x : BanachSpectrum ((a.subatlas P hP).saturatedAtlas.algebra (a.subatlasRecognitionChartIndex hP V k))) :
    V.chart (((a.subatlasRecognitionDomainCover hP V).obj k).spectrumMap x) =
      (a.subatlas P hP).saturatedAtlas.chart (a.subatlasRecognitionChartIndex hP V k) x :=
  a.subatlasRecognitionComponent_over_ambient hP V _ x

theorem subatlasRecognitionDomainCover_obj_locus
    (k : Fin (a.subatlasRecognitionDomainCover hP V).size) :
    ((a.subatlasRecognitionDomainCover hP V).obj k).locus =
      V.chart ⁻¹' Set.range ((a.subatlas P hP).saturatedAtlas.chart (a.subatlasRecognitionChartIndex hP V k)) :=
  a.subatlasRecognitionComponent_locus hP V _

/-- The finite union of these actual selected-saturation chart ranges is
exactly the original recognized chart's unchanged literal ambient locus. -/
theorem subatlasRecognitionChartIndex_covers :
    (⋃ k, Set.range ((a.subatlas P hP).saturatedAtlas.chart (a.subatlasRecognitionChartIndex hP V k))) =
      V.locus := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, y, rfl⟩ := Set.mem_iUnion.mp hx
    exact V.range_chart.subset
      ⟨((a.subatlasRecognitionDomainCover hP V).obj k).spectrumMap y,
        a.subatlasRecognitionDomainCover_over_ambient hP V k y⟩
  · intro hx
    obtain ⟨y, rfl⟩ := V.range_chart.symm ▸ hx
    obtain ⟨k, hk⟩ := (a.subatlasRecognitionDomainCover hP V).covers y (Set.mem_univ y)
    have hk' := (congrArg (fun S : Set (BanachSpectrum V.algebra) => y ∈ S)
      (a.subatlasRecognitionDomainCover_obj_locus hP V k)).mp hk
    exact Set.mem_iUnion.mpr ⟨k, hk'⟩

theorem subatlasRecognitionChartIndex_subset
    (k : Fin (a.subatlasRecognitionDomainCover hP V).size) :
    Set.range ((a.subatlas P hP).saturatedAtlas.chart
      (a.subatlasRecognitionChartIndex hP V k)) ⊆ V.locus := by
  intro x hx
  exact a.subatlasRecognitionChartIndex_covers hP V ▸ Set.mem_iUnion.mpr ⟨k, hx⟩

end Langlands.Analytic.IndexedAffinoidAtlas
