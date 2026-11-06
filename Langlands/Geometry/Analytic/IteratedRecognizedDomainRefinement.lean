import Langlands.Geometry.Analytic.RecognizedDomainAffinoidRealization

/-! # Actual finite original-chart refinements after iterated recognition -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)
  (W : a.fullRecognitionAtlas.saturatedAtlas.RecognizedSubset)

/-- Each original component of the iterated recognized chart is an actual
local-domain presentation in the first full recognition atlas. -/
def iteratedRecognitionLocalParent (i : Fin W.property.cover.size) :
    LocalDomain a.fullRecognitionAtlas :=
  a.fullRecognitionAtlas.saturatedRepresentative (W.property.cover.index i)

/-- The already constructed finite original-local-domain charts of each
actual component domain, with indices in the first saturated atlas. -/
def iteratedRecognitionInnerGluing (i : Fin W.property.cover.size) :
    FiniteChartGluingData a.saturatedAtlas :=
  a.fullRecognitionDomainGluing
    (a.iteratedRecognitionLocalParent W i).index
    (a.iteratedRecognitionLocalParent W i).domain

/-- This inner realization has exactly the algebra of the outer component
as parent, with all full bounded component maps constructed. -/
def iteratedRecognitionInnerRealization (i : Fin W.property.cover.size) :
    (a.iteratedRecognitionInnerGluing W i).AffinoidRealization :=
  a.fullRecognitionDomainAffinoidRealization
    (a.iteratedRecognitionLocalParent W i).index
    (a.iteratedRecognitionLocalParent W i).domain

/-- The finite dependent family of outer and inner component indices. -/
abbrev IteratedRecognitionComponentIndex :=
  (i : Fin W.property.cover.size) × Fin (a.iteratedRecognitionInnerGluing W i).size

/-- Extend each inner full domain through the actual outer component,
retaining its original saturated-chart algebra and both structural maps. -/
def iteratedRecognitionComponent (t : a.IteratedRecognitionComponentIndex W) :
    Domain K W.algebra :=
  (W.property.componentDomain t.1).extend
    ((a.iteratedRecognitionInnerRealization W t.1).domainCover.obj t.2)

@[simp]
theorem iteratedRecognitionComponent_algebra (t : a.IteratedRecognitionComponentIndex W) :
    (a.iteratedRecognitionComponent W t).algebra =
      a.saturatedAtlas.algebra ((a.iteratedRecognitionInnerGluing W t.1).index t.2) := rfl

/-- The unchanged bounded structural map is the full composite through
the actual outer component algebra. -/
theorem iteratedRecognitionComponent_baseMap (t : a.IteratedRecognitionComponentIndex W) :
    (a.iteratedRecognitionComponent W t).baseMap =
      ((a.iteratedRecognitionInnerRealization W t.1).restriction t.2).comp
        (W.property.componentDomain t.1).baseMap := rfl

/-- The extended component recovers its original first-saturation chart
under the actual iterated-parent chart. -/
theorem iteratedRecognitionComponent_over_ambient
    (t : a.IteratedRecognitionComponentIndex W)
    (x : BanachSpectrum
      (a.saturatedAtlas.algebra ((a.iteratedRecognitionInnerGluing W t.1).index t.2))) :
    W.chart ((a.iteratedRecognitionComponent W t).spectrumMap x) =
      a.saturatedAtlas.chart ((a.iteratedRecognitionInnerGluing W t.1).index t.2) x := by
  let C := W.property.componentDomain t.1
  let I := (a.iteratedRecognitionInnerRealization W t.1).domainCover.obj t.2
  have hs : (C.extend I).spectrumMap x = C.spectrumMap (I.spectrumMap x) :=
    BanachSpectrum.ext fun _ => rfl
  exact (congrArg W.chart hs).trans
    ((W.property.componentDomain_over_ambient t.1 (I.spectrumMap x)).trans
      ((a.iteratedRecognitionInnerRealization W t.1).restriction_chart t.2 x))

/-- Each full component has the precise inverse-image locus of its
original first-saturation chart range. -/
theorem iteratedRecognitionComponent_locus (t : a.IteratedRecognitionComponentIndex W) :
    (a.iteratedRecognitionComponent W t).locus =
      W.chart ⁻¹' Set.range
        (a.saturatedAtlas.chart ((a.iteratedRecognitionInnerGluing W t.1).index t.2)) := by
  let R := a.iteratedRecognitionComponent W t
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := R.represents.2.1.symm ▸ hx
    exact ⟨y, (a.iteratedRecognitionComponent_over_ambient W t y).symm.trans
      (congrArg W.chart hy)⟩
  · rintro ⟨y, hy⟩
    have h : R.spectrumMap y = x :=
      W.isEmbedding_chart.injective
        ((a.iteratedRecognitionComponent_over_ambient W t y).trans hy)
    exact h ▸ R.represents.hasImageIn y

/-- Reindex the actual finite dependent family by a finite ordinal. -/
def iteratedRecognitionComponentEnumeration :
    Fin (Fintype.card (a.IteratedRecognitionComponentIndex W)) ≃
      a.IteratedRecognitionComponentIndex W :=
  (Fintype.equivFin (a.IteratedRecognitionComponentIndex W)).symm

/-- Every point is covered by an actual original-chart full domain.
Coverage is proved by the two successive full-domain covers. -/
def iteratedRecognitionDomainCover :
    Domain.FiniteCover (Domain.whole K W.algebra) where
  size := Fintype.card (a.IteratedRecognitionComponentIndex W)
  obj k := a.iteratedRecognitionComponent W (a.iteratedRecognitionComponentEnumeration W k)
  map k := ⟨(a.iteratedRecognitionComponent W
    (a.iteratedRecognitionComponentEnumeration W k)).baseMap, rfl⟩
  covers x _ := by
    obtain ⟨i, hi⟩ := W.componentCover.covers x (Set.mem_univ x)
    have hi' : x ∈ (W.property.componentDomain i).locus := hi
    obtain ⟨y, hy⟩ := (W.property.componentDomain i).represents.2.1.symm ▸ hi'
    obtain ⟨j, hj⟩ :=
      (a.iteratedRecognitionInnerRealization W i).domainCover.covers y (Set.mem_univ y)
    let t : a.IteratedRecognitionComponentIndex W := ⟨i, j⟩
    refine ⟨(a.iteratedRecognitionComponentEnumeration W).symm t, ?_⟩
    rw [Equiv.apply_symm_apply]
    exact ⟨y, hj, hy⟩

/-- The retained first-saturation chart index of each flattened component. -/
def iteratedRecognitionChartIndex
    (k : Fin (a.iteratedRecognitionDomainCover W).size) : a.saturatedAtlas.Index :=
  let t := a.iteratedRecognitionComponentEnumeration W k
  (a.iteratedRecognitionInnerGluing W t.1).index t.2

@[simp]
theorem iteratedRecognitionDomainCover_obj_algebra
    (k : Fin (a.iteratedRecognitionDomainCover W).size) :
    ((a.iteratedRecognitionDomainCover W).obj k).algebra =
      a.saturatedAtlas.algebra (a.iteratedRecognitionChartIndex W k) := rfl

theorem iteratedRecognitionDomainCover_over_ambient
    (k : Fin (a.iteratedRecognitionDomainCover W).size)
    (x : BanachSpectrum (a.saturatedAtlas.algebra (a.iteratedRecognitionChartIndex W k))) :
    W.chart (((a.iteratedRecognitionDomainCover W).obj k).spectrumMap x) =
      a.saturatedAtlas.chart (a.iteratedRecognitionChartIndex W k) x :=
  a.iteratedRecognitionComponent_over_ambient W _ x

theorem iteratedRecognitionDomainCover_obj_locus
    (k : Fin (a.iteratedRecognitionDomainCover W).size) :
    ((a.iteratedRecognitionDomainCover W).obj k).locus =
      W.chart ⁻¹' Set.range (a.saturatedAtlas.chart (a.iteratedRecognitionChartIndex W k)) :=
  a.iteratedRecognitionComponent_locus W _

/-- The finite union of these actual first-saturation chart ranges is
exactly the iterated recognized chart's unchanged literal ambient locus. -/
theorem iteratedRecognitionChartIndex_covers :
    (⋃ k, Set.range (a.saturatedAtlas.chart (a.iteratedRecognitionChartIndex W k))) =
      W.locus := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, y, rfl⟩ := Set.mem_iUnion.mp hx
    exact W.range_chart.subset
      ⟨((a.iteratedRecognitionDomainCover W).obj k).spectrumMap y,
        a.iteratedRecognitionDomainCover_over_ambient W k y⟩
  · intro hx
    obtain ⟨y, rfl⟩ := W.range_chart.symm ▸ hx
    obtain ⟨k, hk⟩ := (a.iteratedRecognitionDomainCover W).covers y (Set.mem_univ y)
    have hk' := (congrArg (fun S : Set (BanachSpectrum W.algebra) => y ∈ S)
      (a.iteratedRecognitionDomainCover_obj_locus W k)).mp hk
    exact Set.mem_iUnion.mpr ⟨k, hk'⟩

end Langlands.Analytic.IndexedAffinoidAtlas
