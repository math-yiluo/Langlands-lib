import Langlands.Geometry.Analytic.SubatlasRecognizedAffinoidRealization
import Langlands.Geometry.Analytic.AffinoidRealizationSpecialCover
import Langlands.Geometry.Analytic.AtlasIntersectionFiniteRecognition

/-! # Reverse recognition from a locally refining selected subatlas -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)
  (P : a.Index → Prop) (hP : a.IsLocallyRefiningSelection P)

/-- The selected saturated algebra and the presentation chosen by the
original saturation are compared by actual inverse local-domain arrows. -/
def subatlasSaturatedOriginalEquiv (s : (a.subatlas P hP).saturatedAtlas.Index) :
    BoundedAlgEquiv K ((a.subatlas P hP).saturatedAtlas.algebra s)
      (a.saturatedAtlas.algebra (a.subatlasSaturatedOriginalIndex P hP s)) :=
  a.localDomainSaturatedEquiv
    (a.subatlasLocalDomain P hP ((a.subatlas P hP).saturatedRepresentative s))

theorem subatlasSaturatedOriginalEquiv_over_ambient
    (s : (a.subatlas P hP).saturatedAtlas.Index)
    (x : BanachSpectrum
      (a.saturatedAtlas.algebra (a.subatlasSaturatedOriginalIndex P hP s))) :
    (a.subatlas P hP).saturatedAtlas.chart s
        ((a.subatlasSaturatedOriginalEquiv P hP s).spectrumHomeomorph x) =
      a.saturatedAtlas.chart (a.subatlasSaturatedOriginalIndex P hP s) x := by
  let L := a.subatlasLocalDomain P hP ((a.subatlas P hP).saturatedRepresentative s)
  let S := a.subatlasSaturatedOriginalIndex P hP s
  exact (LocalDomain.isoOfLocusEq L (a.saturatedRepresentative S)
    (a.saturatedRepresentative_locus S).symm).inv.ambientMap_naturality x

/-- Uniqueness of actual local-domain arrows proves naturality of the
complete bounded comparison maps, without spectrum faithfulness. -/
theorem subatlasSaturatedOriginalEquiv_naturality
    (s t : (a.subatlas P hP).saturatedAtlas.Index)
    (hst : Set.range ((a.subatlas P hP).saturatedAtlas.chart s) ⊆
      Set.range ((a.subatlas P hP).saturatedAtlas.chart t)) :
    (a.saturatedAtlas.restriction
      (a.subatlasSaturatedOriginalIndex P hP s)
      (a.subatlasSaturatedOriginalIndex P hP t)
      ((a.subatlasSaturatedOriginalIndex_range P hP s).subset.trans
        (hst.trans (a.subatlasSaturatedOriginalIndex_range P hP t).symm.subset))).comp
          (a.subatlasSaturatedOriginalEquiv P hP t).toBoundedAlgHom =
      (a.subatlasSaturatedOriginalEquiv P hP s).toBoundedAlgHom.comp
        ((a.subatlas P hP).saturatedAtlas.restriction s t hst) := by
  let S := a.subatlasSaturatedOriginalIndex P hP s
  let T := a.subatlasSaturatedOriginalIndex P hP t
  let L := a.subatlasLocalDomain P hP ((a.subatlas P hP).saturatedRepresentative s)
  let M := a.subatlasLocalDomain P hP ((a.subatlas P hP).saturatedRepresentative t)
  let q := LocalDomain.isoOfLocusEq L (a.saturatedRepresentative S)
    (a.saturatedRepresentative_locus S).symm
  let r := LocalDomain.isoOfLocusEq M (a.saturatedRepresentative T)
    (a.saturatedRepresentative_locus T).symm
  let f := (a.subatlasLocalDomainFunctor P hP).map
    ((a.subatlas P hP).saturatedInclusion s t hst)
  let g := a.saturatedInclusion S T
    ((a.subatlasSaturatedOriginalIndex_range P hP s).subset.trans
      (hst.trans (a.subatlasSaturatedOriginalIndex_range P hP t).symm.subset))
  have h : g ≫ r.inv = q.inv ≫ f :=
    @Subsingleton.elim (LocalDomain.Inclusion (a.saturatedRepresentative S) M)
      inferInstance _ _
  have hr := congrArg LocalDomain.Inclusion.restriction h
  change g.restriction.comp r.inv.restriction = q.inv.restriction.comp f.restriction at hr
  rw [a.subatlasLocalDomainFunctor_map_restriction] at hr
  exact hr

variable {P} (V : (a.subatlas P hP).saturatedAtlas.RecognizedSubset)

/-- Every selected saturated chart contained in V becomes a full domain
over the unchanged V algebra with its original-saturation presentation. -/
def subatlasReverseChartDomain
    (s : (a.subatlas P hP).saturatedAtlas.Index)
    (hs : Set.range ((a.subatlas P hP).saturatedAtlas.chart s) ⊆ V.locus) :
    Domain K V.algebra where
  algebra := a.saturatedAtlas.algebra (a.subatlasSaturatedOriginalIndex P hP s)
  baseMap := (a.subatlasSaturatedOriginalEquiv P hP s).toBoundedAlgHom.comp
    (V.originalRestriction s hs)
  locus := V.chart ⁻¹' Set.range
    (a.saturatedAtlas.chart (a.subatlasSaturatedOriginalIndex P hP s))
  represents := by
    rw [a.subatlasSaturatedOriginalIndex_range]
    exact (V.originalDomain s hs).represents.postcomp_equiv
      (a.subatlasSaturatedOriginalEquiv P hP s)

theorem subatlasReverseChartDomain_over_ambient
    (s : (a.subatlas P hP).saturatedAtlas.Index)
    (hs : Set.range ((a.subatlas P hP).saturatedAtlas.chart s) ⊆ V.locus)
    (x : BanachSpectrum
      (a.saturatedAtlas.algebra (a.subatlasSaturatedOriginalIndex P hP s))) :
    V.chart ((a.subatlasReverseChartDomain hP V s hs).spectrumMap x) =
      a.saturatedAtlas.chart (a.subatlasSaturatedOriginalIndex P hP s) x :=
  (V.chart_originalRestriction s hs
    ((a.subatlasSaturatedOriginalEquiv P hP s).spectrumHomeomorph x)).trans
      (a.subatlasSaturatedOriginalEquiv_over_ambient P hP s x)

/-- Transported component restrictions commute with every selected
saturated inclusion as entire bounded maps over V. -/
theorem subatlasReverseChartDomain_naturality
    (s t : (a.subatlas P hP).saturatedAtlas.Index)
    (hs : Set.range ((a.subatlas P hP).saturatedAtlas.chart s) ⊆ V.locus)
    (ht : Set.range ((a.subatlas P hP).saturatedAtlas.chart t) ⊆ V.locus)
    (hst : Set.range ((a.subatlas P hP).saturatedAtlas.chart s) ⊆
      Set.range ((a.subatlas P hP).saturatedAtlas.chart t)) :
    (a.saturatedAtlas.restriction
      (a.subatlasSaturatedOriginalIndex P hP s)
      (a.subatlasSaturatedOriginalIndex P hP t)
      ((a.subatlasSaturatedOriginalIndex_range P hP s).subset.trans
        (hst.trans (a.subatlasSaturatedOriginalIndex_range P hP t).symm.subset))).comp
          (a.subatlasReverseChartDomain hP V t ht).baseMap =
      (a.subatlasReverseChartDomain hP V s hs).baseMap := by
  ext x
  exact (congrArg
    (fun q : BoundedAlgHom K ((a.subatlas P hP).saturatedAtlas.algebra t)
      (a.saturatedAtlas.algebra (a.subatlasSaturatedOriginalIndex P hP s)) =>
        q (V.originalRestriction t ht x))
    (a.subatlasSaturatedOriginalEquiv_naturality P hP s t hst)).trans
      (congrArg (fun q : BoundedAlgHom K V.algebra
        ((a.subatlas P hP).saturatedAtlas.algebra s) =>
          (a.subatlasSaturatedOriginalEquiv P hP s) (q x))
        (V.originalRestriction_naturality t s ht hs hst))

/-- Keep the selected recognition cover and its overlaps, and change only
their saturated presentations to those in the original atlas. -/
def subatlasReverseRecognitionGluing : FiniteChartGluingData a.saturatedAtlas where
  size := V.property.cover.size
  index i := a.subatlasSaturatedOriginalIndex P hP (V.property.cover.index i)
  overlap i j := a.subatlasSaturatedOriginalIndex P hP (V.property.cover.overlap i j)
  overlap_range i j := by
    rw [a.subatlasSaturatedOriginalIndex_range, V.property.cover.overlap_range,
      a.subatlasSaturatedOriginalIndex_range, a.subatlasSaturatedOriginalIndex_range]

theorem subatlasReverseRecognitionGluing_locus :
    (a.subatlasReverseRecognitionGluing hP V).locus = V.locus := by
  change (⋃ i, Set.range (a.saturatedAtlas.chart
    (a.subatlasSaturatedOriginalIndex P hP (V.property.cover.index i)))) = V.locus
  simp_rw [a.subatlasSaturatedOriginalIndex_range]
  exact V.property.cover_locus

/-- The transported family has an actual finite realization over the
unchanged selected recognized algebra and its unchanged ambient chart. -/
def subatlasReverseRecognitionAffinoidRealization :
    (a.subatlasReverseRecognitionGluing hP V).AffinoidRealization where
  algebra := V.algebra
  chart := V.chart
  isEmbedding_chart := V.isEmbedding_chart
  range_chart := V.range_chart.trans (a.subatlasReverseRecognitionGluing_locus hP V).symm
  restriction i := (a.subatlasReverseChartDomain hP V
    (V.property.cover.index i) (V.component_subset i)).baseMap
  restriction_chart i x := a.subatlasReverseChartDomain_over_ambient hP V
    (V.property.cover.index i) (V.component_subset i) x
  represents i := (a.subatlasReverseChartDomain hP V
    (V.property.cover.index i) (V.component_subset i)).represents
  compatible i j := by
    let d := V.property.cover
    have hO : Set.range ((a.subatlas P hP).saturatedAtlas.chart (d.overlap i j)) ⊆ V.locus :=
      (d.overlap_subset_left i j).trans (V.component_subset i)
    exact (a.subatlasReverseChartDomain_naturality hP V
      (d.overlap i j) (d.index i) hO (V.component_subset i)
        (d.overlap_subset_left i j)).trans
      (a.subatlasReverseChartDomain_naturality hP V
        (d.overlap i j) (d.index j) hO (V.component_subset j)
          (d.overlap_subset_right i j)).symm

theorem subatlasReverseRecognitionGluing_isSpecialCover :
    (a.subatlasReverseRecognitionGluing hP V).IsSpecialCover :=
  (a.subatlasReverseRecognitionAffinoidRealization hP V).isSpecialCover

/-- Reverse recognition is constructed intrinsically, without a supplied
recognition or section-algebra comparison over the original atlas. -/
def subatlasReverseRecognizedSubset : a.saturatedAtlas.RecognizedSubset :=
  (a.subatlasReverseRecognitionAffinoidRealization hP V).recognizedSubset

@[simp]
theorem subatlasReverseRecognizedSubset_locus :
    (a.subatlasReverseRecognizedSubset hP V).locus = V.locus :=
  a.subatlasReverseRecognitionGluing_locus hP V

def subatlasReverseRecognizedSubsetEquiv :
    BoundedAlgEquiv K V.algebra (a.subatlasReverseRecognizedSubset hP V).algebra :=
  (a.subatlasReverseRecognitionAffinoidRealization hP V).recognitionEquiv

theorem subatlasReverseRecognizedSubset_chart
    (x : BanachSpectrum (a.subatlasReverseRecognizedSubset hP V).algebra) :
    (a.subatlasReverseRecognizedSubset hP V).chart x =
      V.chart ((a.subatlasReverseRecognizedSubsetEquiv hP V).spectrumHomeomorph x) :=
  (a.subatlasReverseRecognitionAffinoidRealization hP V).recognizedSubset_chart x

end Langlands.Analytic.IndexedAffinoidAtlas
