import Langlands.Geometry.Analytic.SubatlasDomainAffinoidRealization
import Langlands.Geometry.Analytic.RecognizedDomainClosure

/-! # Recognition of original local domains through a selected atlas -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  {P : a.Index → Prop} (hP : a.IsLocallyRefiningSelection P)

namespace SelectedChartCover

variable {parent : a.Index} (c : a.SelectedChartCover P parent)
  (U : Domain K (a.algebra parent))

/-- The actual overlap quotient is bounded equivalent to the presentation
chosen for its unchanged literal local-domain locus. -/
def saturatedDomainOverlapEquiv (i j : Fin c.size) :
    BoundedAlgEquiv K
      ((c.saturatedDomainComponent hP U i).inter
        (c.saturatedDomainComponent hP U j)).algebra
      ((a.subatlas P hP).saturatedAtlas.algebra ((c.saturatedDomainGluing hP U).overlap i j)) :=
  (a.subatlas P hP).localDomainSaturatedEquiv (c.saturatedDomainOverlap hP U i j)

/-- The first stored atlas restriction is the entire left pushout leg,
followed by the actual bounded comparison to the chosen overlap algebra. -/
theorem saturatedDomainGluing_leftRestriction (i j : Fin c.size) :
    (c.saturatedDomainGluing hP U).leftRestriction i j =
      (c.saturatedDomainOverlapEquiv hP U i j).toBoundedAlgHom.comp
        (AffinoidPushout.leftMap
          (c.saturatedDomainComponent hP U i).baseMap
          (c.saturatedDomainComponent hP U j).baseMap) := by
  let d := c.saturatedDomainGluing hP U
  let E := c.saturatedDomainComponent hP U i
  let F := c.saturatedDomainComponent hP U j
  let Z := (a.subatlas P hP).saturatedRepresentative (c.saturatedDomainIndex hP U i)
  let R : Domain K Z.algebra := E.relative (E.inter F) (E.interLeft F)
  let L := c.saturatedDomainOverlap hP U i j
  let e := LocalDomain.isoOfLocusEq L
    ((a.subatlas P hP).saturatedRepresentative (d.overlap i j))
    ((a.subatlas P hP).saturatedRepresentative_locus (d.overlap i j)).symm
  have h : e.inv ≫ Z.extendInclusion R =
      (a.subatlas P hP).saturatedInclusion (d.overlap i j) (d.index i) (d.overlap_subset_left i j) :=
    @Subsingleton.elim
      (LocalDomain.Inclusion ((a.subatlas P hP).saturatedRepresentative (d.overlap i j)) Z)
      inferInstance _ _
  exact (congrArg LocalDomain.Inclusion.restriction h).symm

/-- The second entire restriction is recovered by cancellation of the full
component representation, using the pushout's structural equation. -/
theorem saturatedDomainGluing_rightRestriction (i j : Fin c.size) :
    (c.saturatedDomainGluing hP U).rightRestriction i j =
      (c.saturatedDomainOverlapEquiv hP U i j).toBoundedAlgHom.comp
        (AffinoidPushout.rightMap
          (c.saturatedDomainComponent hP U i).baseMap
          (c.saturatedDomainComponent hP U j).baseMap) := by
  let d := c.saturatedDomainGluing hP U
  let E := c.saturatedDomainComponent hP U i
  let F := c.saturatedDomainComponent hP U j
  let e := c.saturatedDomainOverlapEquiv hP U i j
  apply F.represents.hom_ext ((a.subatlas P hP).saturatedAtlas.algebra (d.overlap i j))
  ext x
  have hc := congrArg
    (fun q : BoundedAlgHom K U.algebra ((a.subatlas P hP).saturatedAtlas.algebra (d.overlap i j)) => q x)
    ((c.saturatedDomainAffinoidRealization hP U).compatible i j)
  have hl := congrArg
    (fun q : BoundedAlgHom K E.algebra ((a.subatlas P hP).saturatedAtlas.algebra (d.overlap i j)) =>
      q (E.baseMap x))
    (c.saturatedDomainGluing_leftRestriction hP U i j)
  have hp := congrArg
    (fun q : BoundedAlgHom K U.algebra (E.inter F).algebra => e (q x))
    (AffinoidPushout.condition E.baseMap F.baseMap)
  exact hc.symm.trans (hl.trans hp)

/-- The genuine completed-tensor map is the actual pushout quotient map
postcomposed with the constructed bounded equivalence. -/
theorem saturatedDomainGluing_overlapTensorMap (i j : Fin c.size) :
    (c.saturatedDomainGluing hP U).overlapTensorMap i j =
      (c.saturatedDomainOverlapEquiv hP U i j).toBoundedAlgHom.comp
        (AffinoidPushout.tensorMap
          (c.saturatedDomainComponent hP U i).baseMap
          (c.saturatedDomainComponent hP U j).baseMap) := by
  let d := c.saturatedDomainGluing hP U
  let E := c.saturatedDomainComponent hP U i
  let F := c.saturatedDomainComponent hP U j
  let e := c.saturatedDomainOverlapEquiv hP U i j
  apply CompletedTensorAlgebra.hom_ext
  · ext x
    have ht := congrArg
      (fun q : BoundedAlgHom K E.algebra ((a.subatlas P hP).saturatedAtlas.algebra (d.overlap i j)) => q x)
      (d.overlapTensorMap_comp_leftMap i j)
    have hl := congrArg
      (fun q : BoundedAlgHom K E.algebra ((a.subatlas P hP).saturatedAtlas.algebra (d.overlap i j)) => q x)
      (c.saturatedDomainGluing_leftRestriction hP U i j)
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
      (c.saturatedDomainGluing_rightRestriction hP U i j)
    have hp := congrArg
      (fun q : BoundedAlgHom K F.algebra (E.inter F).algebra => e (q x))
      (AffinoidPushout.tensorMap_comp_rightMap E.baseMap F.baseMap)
    exact ht.trans (hr.trans hp.symm)

/-- Admissibility includes surjectivity and the actual positive uniform
quotient-norm comparison, transported through a bounded inverse. -/
theorem saturatedDomainGluing_tensor_isAdmissibleEpi
    (i j : Fin c.size) :
    ((c.saturatedDomainGluing hP U).overlapTensorMap i j).IsAdmissibleEpi := by
  let e := c.saturatedDomainOverlapEquiv hP U i j
  have he : e.toBoundedAlgHom.IsAdmissibleEpi := by
    apply e.toBoundedAlgHom.isAdmissibleEpi_of_bounded_section e.symm.toBoundedAlgHom
    ext x
    exact e.apply_symm_apply x
  rw [c.saturatedDomainGluing_overlapTensorMap]
  exact BoundedAlgHom.IsAdmissibleEpi.comp _ _
    (AffinoidPushout.tensorMap_isAdmissibleEpi _ _) he

/-- The constructed parent spectrum supplies the Hausdorff topology on the
finite union, without a Hausdorff hypothesis on the ambient space. -/
theorem saturatedDomainGluing_isSpecialCover :
    (c.saturatedDomainGluing hP U).IsSpecialCover :=
  ⟨(c.saturatedDomainAffinoidRealization hP U).locusHomeomorph.symm.t2Space,
    c.saturatedDomainGluing_tensor_isAdmissibleEpi hP U⟩

/-- Every original local full domain is an actual special subset of the
selected saturation, witnessed by the constructed finite quotient cover. -/
def saturatedDomainSpecialSubset : (a.subatlas P hP).saturatedAtlas.SpecialSubset :=
  ⟨(⟨parent, U⟩ : LocalDomain a).locus, c.saturatedDomainGluing hP U,
    c.saturatedDomainGluing_locus hP U,
    c.saturatedDomainGluing_isSpecialCover hP U⟩

@[simp]
theorem saturatedDomainSpecialSubset_val :
    (c.saturatedDomainSpecialSubset hP U).val = (⟨parent, U⟩ : LocalDomain a).locus := rfl

/-- The finite realization and its constructed special cover give all
three intrinsic recognition conditions on the unchanged old domain locus. -/
theorem saturatedDomainSpecialSubset_isRecognized :
    (c.saturatedDomainSpecialSubset hP U).IsRecognized :=
  (c.saturatedDomainSpecialSubset hP U).isRecognized_of_affinoidRealization
    (c.saturatedDomainGluing hP U) (c.saturatedDomainGluing_locus hP U)
    (c.saturatedDomainGluing_isSpecialCover hP U)
    (c.saturatedDomainAffinoidRealization hP U)

/-- Every old local full domain is recognized by the selected local-domain
saturation, with no recognition witness supplied as an input. -/
def saturatedDomainRecognizedSubset : (a.subatlas P hP).saturatedAtlas.RecognizedSubset :=
  ⟨c.saturatedDomainSpecialSubset hP U, c.saturatedDomainSpecialSubset_isRecognized hP U⟩

@[simp]
theorem saturatedDomainRecognizedSubset_locus :
    (c.saturatedDomainRecognizedSubset hP U).locus =
      (⟨parent, U⟩ : LocalDomain a).locus := rfl

/-- The original full-domain algebra is bounded equivalent to the actual
presentation constructed from the canonical selected section algebra. -/
def saturatedDomainAlgebraEquiv :
    BoundedAlgEquiv K U.algebra (c.saturatedDomainRecognizedSubset hP U).algebra :=
  ((c.saturatedDomainSpecialSubset hP U).realizationSectionEquiv
    (c.saturatedDomainGluing hP U) (c.saturatedDomainGluing_locus hP U)
    (c.saturatedDomainAffinoidRealization hP U)).trans
      (c.saturatedDomainRecognizedSubset hP U).property.algebraEquiv.symm

/-- The constructed algebra comparison identifies the recognized chart
with the unchanged old domain ambient map on every spectrum point. -/
theorem saturatedDomainRecognizedSubset_chart
    (x : BanachSpectrum (c.saturatedDomainRecognizedSubset hP U).algebra) :
    (c.saturatedDomainRecognizedSubset hP U).chart x =
      (⟨parent, U⟩ : LocalDomain a).ambientMap
        ((c.saturatedDomainAlgebraEquiv hP U).spectrumHomeomorph x) :=
  (c.saturatedDomainSpecialSubset hP U).chart_affinoidRealization
    (c.saturatedDomainRecognizedSubset hP U).property.affinoid
    (c.saturatedDomainRecognizedSubset hP U).property.bijective
    (c.saturatedDomainGluing hP U) (c.saturatedDomainGluing_locus hP U)
    (c.saturatedDomainAffinoidRealization hP U) x

end SelectedChartCover

variable (a)

/-- A finite selected cover is constructed for the parent of every old
local domain, so every old local domain has a recognized selected presentation. -/
def subatlasRecognizedLocalDomain (U : LocalDomain a) :
    (a.subatlas P hP).saturatedAtlas.RecognizedSubset :=
  (a.selectedChartCover P hP U.index).saturatedDomainRecognizedSubset hP U.domain

@[simp]
theorem subatlasRecognizedLocalDomain_locus (U : LocalDomain a) :
    (a.subatlasRecognizedLocalDomain hP U).locus = U.locus := rfl

def subatlasRecognizedLocalDomainEquiv (U : LocalDomain a) :
    BoundedAlgEquiv K U.algebra (a.subatlasRecognizedLocalDomain hP U).algebra :=
  (a.selectedChartCover P hP U.index).saturatedDomainAlgebraEquiv hP U.domain

theorem subatlasRecognizedLocalDomain_chart (U : LocalDomain a)
    (x : BanachSpectrum (a.subatlasRecognizedLocalDomain hP U).algebra) :
    (a.subatlasRecognizedLocalDomain hP U).chart x =
      U.ambientMap ((a.subatlasRecognizedLocalDomainEquiv hP U).spectrumHomeomorph x) :=
  (a.selectedChartCover P hP U.index).saturatedDomainRecognizedSubset_chart hP U.domain x

end Langlands.Analytic.IndexedAffinoidAtlas
