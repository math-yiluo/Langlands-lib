import Langlands.Geometry.Analytic.RecognizedDomainAffinoidRealization
import Langlands.Geometry.Analytic.AtlasDomainTensorIntersection

/-! # Actual tensor-admissible special covers of recognized-chart domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)
  (V : a.saturatedAtlas.RecognizedSubset) (D : Domain K V.algebra)

/-- The actual overlap quotient is bounded equivalent to the presentation
chosen for its unchanged literal local-domain locus. -/
def fullRecognitionDomainOverlapEquiv (i j : Fin V.property.cover.size) :
    BoundedAlgEquiv K
      ((a.fullRecognitionDomainComponent V D i).inter
        (a.fullRecognitionDomainComponent V D j)).algebra
      (a.saturatedAtlas.algebra ((a.fullRecognitionDomainGluing V D).overlap i j)) :=
  a.localDomainSaturatedEquiv (a.fullRecognitionDomainOverlap V D i j)

/-- The first stored atlas restriction is the entire left pushout leg,
followed by the actual bounded comparison to the chosen overlap algebra. -/
theorem fullRecognitionDomainGluing_leftRestriction (i j : Fin V.property.cover.size) :
    (a.fullRecognitionDomainGluing V D).leftRestriction i j =
      (a.fullRecognitionDomainOverlapEquiv V D i j).toBoundedAlgHom.comp
        (AffinoidPushout.leftMap
          (a.fullRecognitionDomainComponent V D i).baseMap
          (a.fullRecognitionDomainComponent V D j).baseMap) := by
  let d := a.fullRecognitionDomainGluing V D
  let E := a.fullRecognitionDomainComponent V D i
  let F := a.fullRecognitionDomainComponent V D j
  let U := a.saturatedRepresentative (a.fullRecognitionDomainIndex V D i)
  let R : Domain K U.algebra := E.relative (E.inter F) (E.interLeft F)
  let L := a.fullRecognitionDomainOverlap V D i j
  let e := LocalDomain.isoOfLocusEq L
    (a.saturatedRepresentative (d.overlap i j))
    (a.saturatedRepresentative_locus (d.overlap i j)).symm
  have h : e.inv ≫ U.extendInclusion R =
      a.saturatedInclusion (d.overlap i j) (d.index i) (d.overlap_subset_left i j) :=
    @Subsingleton.elim
      (LocalDomain.Inclusion (a.saturatedRepresentative (d.overlap i j)) U)
      inferInstance _ _
  exact (congrArg LocalDomain.Inclusion.restriction h).symm

/-- The second entire restriction is recovered by cancellation of the full
component representation, using the pushout's structural equation. -/
theorem fullRecognitionDomainGluing_rightRestriction (i j : Fin V.property.cover.size) :
    (a.fullRecognitionDomainGluing V D).rightRestriction i j =
      (a.fullRecognitionDomainOverlapEquiv V D i j).toBoundedAlgHom.comp
        (AffinoidPushout.rightMap
          (a.fullRecognitionDomainComponent V D i).baseMap
          (a.fullRecognitionDomainComponent V D j).baseMap) := by
  let d := a.fullRecognitionDomainGluing V D
  let E := a.fullRecognitionDomainComponent V D i
  let F := a.fullRecognitionDomainComponent V D j
  let e := a.fullRecognitionDomainOverlapEquiv V D i j
  apply F.represents.hom_ext (a.saturatedAtlas.algebra (d.overlap i j))
  ext x
  have hc := congrArg
    (fun q : BoundedAlgHom K D.algebra (a.saturatedAtlas.algebra (d.overlap i j)) => q x)
    ((a.fullRecognitionDomainAffinoidRealization V D).compatible i j)
  have hl := congrArg
    (fun q : BoundedAlgHom K E.algebra (a.saturatedAtlas.algebra (d.overlap i j)) =>
      q (E.baseMap x))
    (a.fullRecognitionDomainGluing_leftRestriction V D i j)
  have hp := congrArg
    (fun q : BoundedAlgHom K D.algebra (E.inter F).algebra => e (q x))
    (AffinoidPushout.condition E.baseMap F.baseMap)
  exact hc.symm.trans (hl.trans hp)

/-- The genuine completed-tensor map is the actual pushout quotient map
postcomposed with the constructed bounded equivalence. -/
theorem fullRecognitionDomainGluing_overlapTensorMap (i j : Fin V.property.cover.size) :
    (a.fullRecognitionDomainGluing V D).overlapTensorMap i j =
      (a.fullRecognitionDomainOverlapEquiv V D i j).toBoundedAlgHom.comp
        (AffinoidPushout.tensorMap
          (a.fullRecognitionDomainComponent V D i).baseMap
          (a.fullRecognitionDomainComponent V D j).baseMap) := by
  let d := a.fullRecognitionDomainGluing V D
  let E := a.fullRecognitionDomainComponent V D i
  let F := a.fullRecognitionDomainComponent V D j
  let e := a.fullRecognitionDomainOverlapEquiv V D i j
  apply CompletedTensorAlgebra.hom_ext
  · ext x
    have ht := congrArg
      (fun q : BoundedAlgHom K E.algebra (a.saturatedAtlas.algebra (d.overlap i j)) => q x)
      (d.overlapTensorMap_comp_leftMap i j)
    have hl := congrArg
      (fun q : BoundedAlgHom K E.algebra (a.saturatedAtlas.algebra (d.overlap i j)) => q x)
      (a.fullRecognitionDomainGluing_leftRestriction V D i j)
    have hp := congrArg
      (fun q : BoundedAlgHom K E.algebra (E.inter F).algebra => e (q x))
      (AffinoidPushout.tensorMap_comp_leftMap E.baseMap F.baseMap)
    exact ht.trans (hl.trans hp.symm)
  · ext x
    have ht := congrArg
      (fun q : BoundedAlgHom K F.algebra (a.saturatedAtlas.algebra (d.overlap i j)) => q x)
      (d.overlapTensorMap_comp_rightMap i j)
    have hr := congrArg
      (fun q : BoundedAlgHom K F.algebra (a.saturatedAtlas.algebra (d.overlap i j)) => q x)
      (a.fullRecognitionDomainGluing_rightRestriction V D i j)
    have hp := congrArg
      (fun q : BoundedAlgHom K F.algebra (E.inter F).algebra => e (q x))
      (AffinoidPushout.tensorMap_comp_rightMap E.baseMap F.baseMap)
    exact ht.trans (hr.trans hp.symm)

/-- Admissibility includes surjectivity and the actual positive uniform
quotient-norm comparison, transported through a bounded inverse. -/
theorem fullRecognitionDomainGluing_tensor_isAdmissibleEpi
    (i j : Fin V.property.cover.size) :
    ((a.fullRecognitionDomainGluing V D).overlapTensorMap i j).IsAdmissibleEpi := by
  let e := a.fullRecognitionDomainOverlapEquiv V D i j
  have he : e.toBoundedAlgHom.IsAdmissibleEpi := by
    apply e.toBoundedAlgHom.isAdmissibleEpi_of_bounded_section e.symm.toBoundedAlgHom
    ext x
    exact e.apply_symm_apply x
  rw [a.fullRecognitionDomainGluing_overlapTensorMap]
  exact BoundedAlgHom.IsAdmissibleEpi.comp _ _
    (AffinoidPushout.tensorMap_isAdmissibleEpi _ _) he

/-- The constructed parent spectrum supplies the Hausdorff topology on the
finite union, without a Hausdorff hypothesis on the ambient space. -/
theorem fullRecognitionDomainGluing_isSpecialCover :
    (a.fullRecognitionDomainGluing V D).IsSpecialCover :=
  ⟨(a.fullRecognitionDomainAffinoidRealization V D).locusHomeomorph.symm.t2Space,
    a.fullRecognitionDomainGluing_tensor_isAdmissibleEpi V D⟩

/-- Every full domain in a recognized chart is an actual special subset of
the saturated atlas, witnessed by the constructed finite quotient cover. -/
def fullRecognitionDomainSpecialSubset : a.saturatedAtlas.SpecialSubset :=
  ⟨V.domainLocus D, a.fullRecognitionDomainGluing V D,
    a.fullRecognitionDomainGluing_locus V D,
    a.fullRecognitionDomainGluing_isSpecialCover V D⟩

@[simp]
theorem fullRecognitionDomainSpecialSubset_val :
    (a.fullRecognitionDomainSpecialSubset V D).val = V.domainLocus D := rfl

end Langlands.Analytic.IndexedAffinoidAtlas
