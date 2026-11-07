import Langlands.Geometry.Analytic.SubatlasRecognizedAffinoidRealization
import Langlands.Geometry.Analytic.RecognizedDomainClosure

/-! # Recognition of arbitrary original recognized subsets in a selected atlas -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)
  {P : a.Index → Prop} (hP : a.IsLocallyRefiningSelection P)
  (V : a.saturatedAtlas.RecognizedSubset)

def subatlasRecognitionOverlapEquiv
    (i j : Fin (a.subatlasRecognitionDomainCover hP V).size) :
    BoundedAlgEquiv K
      ((a.subatlasRecognitionCanonicalComponent hP V i).inter
        (a.subatlasRecognitionCanonicalComponent hP V j)).algebra
      ((a.subatlas P hP).saturatedAtlas.algebra ((a.subatlasRecognitionGluing hP V).overlap i j)) :=
  (a.subatlas P hP).localDomainSaturatedEquiv (a.subatlasRecognitionOverlap hP V i j)

theorem subatlasRecognitionGluing_leftRestriction
    (i j : Fin (a.subatlasRecognitionDomainCover hP V).size) :
    (a.subatlasRecognitionGluing hP V).leftRestriction i j =
      (a.subatlasRecognitionOverlapEquiv hP V i j).toBoundedAlgHom.comp
        (AffinoidPushout.leftMap
          (a.subatlasRecognitionCanonicalComponent hP V i).baseMap
          (a.subatlasRecognitionCanonicalComponent hP V j).baseMap) := by
  let d := a.subatlasRecognitionGluing hP V
  let E := a.subatlasRecognitionCanonicalComponent hP V i
  let F := a.subatlasRecognitionCanonicalComponent hP V j
  let U := (a.subatlas P hP).saturatedRepresentative (a.subatlasRecognitionChartIndex hP V i)
  let R : Domain K U.algebra := E.relative (E.inter F) (E.interLeft F)
  let L := a.subatlasRecognitionOverlap hP V i j
  let e := LocalDomain.isoOfLocusEq L ((a.subatlas P hP).saturatedRepresentative (d.overlap i j))
    ((a.subatlas P hP).saturatedRepresentative_locus (d.overlap i j)).symm
  have h : e.inv ≫ U.extendInclusion R =
      (a.subatlas P hP).saturatedInclusion (d.overlap i j) (d.index i) (d.overlap_subset_left i j) :=
    @Subsingleton.elim
      (LocalDomain.Inclusion ((a.subatlas P hP).saturatedRepresentative (d.overlap i j)) U) inferInstance _ _
  exact (congrArg LocalDomain.Inclusion.restriction h).symm

theorem subatlasRecognitionGluing_rightRestriction
    (i j : Fin (a.subatlasRecognitionDomainCover hP V).size) :
    (a.subatlasRecognitionGluing hP V).rightRestriction i j =
      (a.subatlasRecognitionOverlapEquiv hP V i j).toBoundedAlgHom.comp
        (AffinoidPushout.rightMap
          (a.subatlasRecognitionCanonicalComponent hP V i).baseMap
          (a.subatlasRecognitionCanonicalComponent hP V j).baseMap) := by
  let d := a.subatlasRecognitionGluing hP V
  let E := a.subatlasRecognitionCanonicalComponent hP V i
  let F := a.subatlasRecognitionCanonicalComponent hP V j
  let e := a.subatlasRecognitionOverlapEquiv hP V i j
  apply F.represents.hom_ext ((a.subatlas P hP).saturatedAtlas.algebra (d.overlap i j))
  ext x
  have hc := congrArg
    (fun q : BoundedAlgHom K V.algebra ((a.subatlas P hP).saturatedAtlas.algebra (d.overlap i j)) => q x)
    ((a.subatlasRecognitionAffinoidRealization hP V).compatible i j)
  have hl := congrArg
    (fun q : BoundedAlgHom K E.algebra ((a.subatlas P hP).saturatedAtlas.algebra (d.overlap i j)) =>
      q (E.baseMap x)) (a.subatlasRecognitionGluing_leftRestriction hP V i j)
  have hp := congrArg
    (fun q : BoundedAlgHom K V.algebra (E.inter F).algebra => e (q x))
    (AffinoidPushout.condition E.baseMap F.baseMap)
  exact hc.symm.trans (hl.trans hp)

theorem subatlasRecognitionGluing_overlapTensorMap
    (i j : Fin (a.subatlasRecognitionDomainCover hP V).size) :
    (a.subatlasRecognitionGluing hP V).overlapTensorMap i j =
      (a.subatlasRecognitionOverlapEquiv hP V i j).toBoundedAlgHom.comp
        (AffinoidPushout.tensorMap
          (a.subatlasRecognitionCanonicalComponent hP V i).baseMap
          (a.subatlasRecognitionCanonicalComponent hP V j).baseMap) := by
  let d := a.subatlasRecognitionGluing hP V
  let E := a.subatlasRecognitionCanonicalComponent hP V i
  let F := a.subatlasRecognitionCanonicalComponent hP V j
  let e := a.subatlasRecognitionOverlapEquiv hP V i j
  apply CompletedTensorAlgebra.hom_ext
  · ext x
    have ht := congrArg
      (fun q : BoundedAlgHom K E.algebra ((a.subatlas P hP).saturatedAtlas.algebra (d.overlap i j)) => q x)
      (d.overlapTensorMap_comp_leftMap i j)
    have hl := congrArg
      (fun q : BoundedAlgHom K E.algebra ((a.subatlas P hP).saturatedAtlas.algebra (d.overlap i j)) => q x)
      (a.subatlasRecognitionGluing_leftRestriction hP V i j)
    have hp := congrArg
      (fun q : BoundedAlgHom K E.algebra (E.inter F).algebra => e (q x))
      (AffinoidPushout.tensorMap_comp_leftMap E.baseMap F.baseMap)
    exact ht.trans (hl.trans hp.symm)
  · ext x
    have ht := congrArg
      (fun q : BoundedAlgHom K F.algebra ((a.subatlas P hP).saturatedAtlas.algebra (d.overlap i j)) => q x)
      (d.overlapTensorMap_comp_rightMap i j)
    have hr := congrArg
      (fun q : BoundedAlgHom K F.algebra ((a.subatlas P hP).saturatedAtlas.algebra (d.overlap i j)) => q x)
      (a.subatlasRecognitionGluing_rightRestriction hP V i j)
    have hp := congrArg
      (fun q : BoundedAlgHom K F.algebra (E.inter F).algebra => e (q x))
      (AffinoidPushout.tensorMap_comp_rightMap E.baseMap F.baseMap)
    exact ht.trans (hr.trans hp.symm)

theorem subatlasRecognitionGluing_tensor_isAdmissibleEpi
    (i j : Fin (a.subatlasRecognitionDomainCover hP V).size) :
    ((a.subatlasRecognitionGluing hP V).overlapTensorMap i j).IsAdmissibleEpi := by
  let e := a.subatlasRecognitionOverlapEquiv hP V i j
  have he : e.toBoundedAlgHom.IsAdmissibleEpi := by
    apply e.toBoundedAlgHom.isAdmissibleEpi_of_bounded_section e.symm.toBoundedAlgHom
    ext x
    exact e.apply_symm_apply x
  rw [a.subatlasRecognitionGluing_overlapTensorMap]
  exact BoundedAlgHom.IsAdmissibleEpi.comp _ _
    (AffinoidPushout.tensorMap_isAdmissibleEpi _ _) he

theorem subatlasRecognitionGluing_isSpecialCover :
    (a.subatlasRecognitionGluing hP V).IsSpecialCover :=
  ⟨(a.subatlasRecognitionAffinoidRealization hP V).locusHomeomorph.symm.t2Space,
    a.subatlasRecognitionGluing_tensor_isAdmissibleEpi hP V⟩

/-- The literal original recognized locus has an actual special cover in
the selected local-domain saturation. -/
def subatlasRecognitionSpecialSubset : (a.subatlas P hP).saturatedAtlas.SpecialSubset :=
  ⟨V.locus, a.subatlasRecognitionGluing hP V, a.subatlasRecognitionGluing_locus hP V,
    a.subatlasRecognitionGluing_isSpecialCover hP V⟩

/-- Construct a selected recognized presentation for every original recognized
subset, supplying all three intrinsic recognition conditions. -/
def subatlasRecognizedSubset : (a.subatlas P hP).saturatedAtlas.RecognizedSubset :=
  ⟨a.subatlasRecognitionSpecialSubset hP V,
    (a.subatlasRecognitionSpecialSubset hP V).isRecognized_of_affinoidRealization
      (a.subatlasRecognitionGluing hP V) (a.subatlasRecognitionGluing_locus hP V)
      (a.subatlasRecognitionGluing_isSpecialCover hP V)
      (a.subatlasRecognitionAffinoidRealization hP V)⟩

@[simp]
theorem subatlasRecognizedSubset_locus :
    (a.subatlasRecognizedSubset hP V).locus = V.locus := rfl

/-- The original recognized algebra and its constructed selected presentation
are compared by actual bounded mutually inverse algebra maps. -/
def subatlasRecognizedSubsetEquiv :
    BoundedAlgEquiv K V.algebra (a.subatlasRecognizedSubset hP V).algebra :=
  ((a.subatlasRecognitionSpecialSubset hP V).realizationSectionEquiv
    (a.subatlasRecognitionGluing hP V) (a.subatlasRecognitionGluing_locus hP V)
    (a.subatlasRecognitionAffinoidRealization hP V)).trans
      (a.subatlasRecognizedSubset hP V).property.algebraEquiv.symm

theorem subatlasRecognizedSubset_chart
    (x : BanachSpectrum (a.subatlasRecognizedSubset hP V).algebra) :
    (a.subatlasRecognizedSubset hP V).chart x =
      V.chart ((a.subatlasRecognizedSubsetEquiv hP V).spectrumHomeomorph x) :=
  (a.subatlasRecognitionSpecialSubset hP V).chart_affinoidRealization
    (a.subatlasRecognizedSubset hP V).property.affinoid
    (a.subatlasRecognizedSubset hP V).property.bijective
    (a.subatlasRecognitionGluing hP V) (a.subatlasRecognitionGluing_locus hP V)
    (a.subatlasRecognitionAffinoidRealization hP V) x

end Langlands.Analytic.IndexedAffinoidAtlas
