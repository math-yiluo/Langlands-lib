import Langlands.Geometry.Analytic.RecognizedDomainClosure
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainComparison

/-! # Specialness and recognition from an actual finite affinoid realization -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData.AffinoidRealization

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  {d : FiniteChartGluingData a} (c : d.AffinoidRealization)

/-- The actual original overlap and the pushout intersection represent
the same literal subset of the unchanged parent spectrum. -/
theorem inter_locus_eq_overlapDomain (i j : Fin d.size) :
    ((c.componentDomain i).inter (c.componentDomain j)).locus =
      (c.overlapDomain i j).locus := by
  change (c.chart ⁻¹' Set.range (a.chart (d.index i))) ∩
      (c.chart ⁻¹' Set.range (a.chart (d.index j))) =
    c.chart ⁻¹' Set.range (a.chart (d.overlap i j))
  rw [d.overlap_range]
  rfl

/-- Full represented-domain uniqueness constructs both bounded maps;
no equality of algebra maps is inferred from spectrum points. -/
def overlapEquiv (i j : Fin d.size) :
    BoundedAlgEquiv K
      ((c.componentDomain i).inter (c.componentDomain j)).algebra
      (a.algebra (d.overlap i j)) :=
  Domain.boundedEquivOfLocusEq _ _ (c.inter_locus_eq_overlapDomain i j)

/-- The first original overlap restriction is the entire first pushout
leg followed by the constructed bounded equivalence. -/
theorem leftRestriction_eq (i j : Fin d.size) :
    d.leftRestriction i j =
      (c.overlapEquiv i j).toBoundedAlgHom.comp
        (AffinoidPushout.leftMap (c.restriction i) (c.restriction j)) := by
  let E := c.componentDomain i
  let F := c.componentDomain j
  let O := c.overlapDomain i j
  let e := Domain.isoOfLocusEq (E.inter F) O (c.inter_locus_eq_overlapDomain i j)
  let ol : O ⟶ E := ⟨d.leftRestriction i j, rfl⟩
  have h : ol = e.inv ≫ E.interLeft F :=
    @Subsingleton.elim (Domain.Inclusion O E) inferInstance _ _
  exact congrArg Domain.Inclusion.restriction h

/-- The second original overlap restriction is the entire second pushout
leg followed by the same constructed bounded equivalence. -/
theorem rightRestriction_eq (i j : Fin d.size) :
    d.rightRestriction i j =
      (c.overlapEquiv i j).toBoundedAlgHom.comp
        (AffinoidPushout.rightMap (c.restriction i) (c.restriction j)) := by
  let E := c.componentDomain i
  let F := c.componentDomain j
  let O := c.overlapDomain i j
  let e := Domain.isoOfLocusEq (E.inter F) O (c.inter_locus_eq_overlapDomain i j)
  let or : O ⟶ F := ⟨d.rightRestriction i j, (c.compatible i j).symm⟩
  have h : or = e.inv ≫ E.interRight F :=
    @Subsingleton.elim (Domain.Inclusion O F) inferInstance _ _
  exact congrArg Domain.Inclusion.restriction h

/-- The genuine completed-tensor overlap map is the admissible pushout
quotient followed by the actual bounded overlap equivalence. -/
theorem overlapTensorMap_eq (i j : Fin d.size) :
    d.overlapTensorMap i j =
      (c.overlapEquiv i j).toBoundedAlgHom.comp
        (AffinoidPushout.tensorMap (c.restriction i) (c.restriction j)) := by
  let E := c.componentDomain i
  let F := c.componentDomain j
  let e := c.overlapEquiv i j
  apply CompletedTensorAlgebra.hom_ext
  · ext x
    have ht := congrArg
      (fun q : BoundedAlgHom K E.algebra (a.algebra (d.overlap i j)) => q x)
      (d.overlapTensorMap_comp_leftMap i j)
    have hl := congrArg
      (fun q : BoundedAlgHom K E.algebra (a.algebra (d.overlap i j)) => q x)
      (c.leftRestriction_eq i j)
    have hp := congrArg
      (fun q : BoundedAlgHom K E.algebra (E.inter F).algebra => e (q x))
      (AffinoidPushout.tensorMap_comp_leftMap E.baseMap F.baseMap)
    exact ht.trans (hl.trans hp.symm)
  · ext x
    have ht := congrArg
      (fun q : BoundedAlgHom K F.algebra (a.algebra (d.overlap i j)) => q x)
      (d.overlapTensorMap_comp_rightMap i j)
    have hr := congrArg
      (fun q : BoundedAlgHom K F.algebra (a.algebra (d.overlap i j)) => q x)
      (c.rightRestriction_eq i j)
    have hp := congrArg
      (fun q : BoundedAlgHom K F.algebra (E.inter F).algebra => e (q x))
      (AffinoidPushout.tensorMap_comp_rightMap E.baseMap F.baseMap)
    exact ht.trans (hr.trans hp.symm)

include c in
theorem overlapTensorMap_isAdmissibleEpi (i j : Fin d.size) :
    (d.overlapTensorMap i j).IsAdmissibleEpi := by
  let e := c.overlapEquiv i j
  have he : e.toBoundedAlgHom.IsAdmissibleEpi := by
    apply e.toBoundedAlgHom.isAdmissibleEpi_of_bounded_section e.symm.toBoundedAlgHom
    ext x
    exact e.apply_symm_apply x
  rw [c.overlapTensorMap_eq]
  exact BoundedAlgHom.IsAdmissibleEpi.comp _ _
    (AffinoidPushout.tensorMap_isAdmissibleEpi _ _) he

include c in
/-- An actual finite affinoid realization proves specialness intrinsically,
including Hausdorffness of the literal union. -/
theorem isSpecialCover : d.IsSpecialCover :=
  ⟨c.locusHomeomorph.symm.t2Space, c.overlapTensorMap_isAdmissibleEpi⟩

def specialSubset : a.SpecialSubset :=
  ⟨d.locus, d, rfl, c.isSpecialCover⟩

/-- The realization supplies all three intrinsic recognition conditions. -/
def recognizedSubset : a.RecognizedSubset :=
  ⟨c.specialSubset, c.specialSubset.isRecognized_of_affinoidRealization
    d rfl c.isSpecialCover c⟩

@[simp]
theorem recognizedSubset_locus : c.recognizedSubset.locus = d.locus := rfl

/-- Recover the realized parent algebra through constructed bounded
mutually inverse maps to the canonical recognized presentation. -/
def recognitionEquiv : BoundedAlgEquiv K c.algebra c.recognizedSubset.algebra :=
  (c.specialSubset.realizationSectionEquiv d rfl c).trans
    c.recognizedSubset.property.algebraEquiv.symm

theorem recognizedSubset_chart (x : BanachSpectrum c.recognizedSubset.algebra) :
    c.recognizedSubset.chart x =
      c.chart (c.recognitionEquiv.spectrumHomeomorph x) :=
  c.specialSubset.chart_affinoidRealization c.recognizedSubset.property.affinoid
    c.recognizedSubset.property.bijective d rfl c x

end Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData.AffinoidRealization
