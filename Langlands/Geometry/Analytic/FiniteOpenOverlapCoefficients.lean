import Langlands.Geometry.Analytic.FiniteOpenModelGluing
import Langlands.Geometry.Analytic.FiniteOpenAlgebraDescentData
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.MatchingAlgebra

/-! # Entire finite-open overlap coefficient comparisons -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}

/-- Equality of entire base maps compares the two actual quotient algebras. -/
def rightEqEquiv (f : BoundedAlgHom K A B) {g g' : BoundedAlgHom K A C} (h : g = g') :
    BoundedAlgEquiv K (algebra f g) (algebra f g') := by
  subst g'
  exact BoundedAlgEquiv.refl K _

omit [CompleteSpace K] in
theorem rightEqEquiv_comp_left (f : BoundedAlgHom K A B)
    {g g' : BoundedAlgHom K A C} (h : g = g') :
    (rightEqEquiv f h).toBoundedAlgHom.comp (leftMap f g) = leftMap f g' := by
  subst g'
  rfl

omit [CompleteSpace K] in
theorem rightEqEquiv_comp_right (f : BoundedAlgHom K A B)
    {g g' : BoundedAlgHom K A C} (h : g = g') :
    (rightEqEquiv f h).toBoundedAlgHom.comp (rightMap f g) = rightMap f g' := by
  subst g'
  rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
  (R : A.atlas.saturatedAtlas.RecognizedSubset)

/-- The complete restrictions from a common original full domain are
coefficient chart changes in the selected recognition source itself. -/
theorem domainRecognition_overlap_source_change
    (D E F : Domain K R.algebra) (r : F ⟶ D) (s : F ⟶ E)
    (W W' : B.atlas.saturatedAtlas.RecognizedSubset)
    (hD : g.baseMap '' (R.chart '' D.locus) ⊆ W.locus)
    (hE : g.baseMap '' (R.chart '' E.locus) ⊆ W'.locus) :
    g.recognitionSource.atlas.IsMapChartChange
      (g.recognitionSourceIndex (g.domainRecognition R D) W
        (g.domainRecognition_admissible R D W hD))
      (g.recognitionSourceIndex (g.domainRecognition R E) W'
        (g.domainRecognition_admissible R E W' hE))
      F.algebra
      (r.restriction.comp (g.domainRecognitionEquiv R D).symm.toBoundedAlgHom)
      (s.restriction.comp (g.domainRecognitionEquiv R E).symm.toBoundedAlgHom) := by
  let I := g.recognitionSourceIndex (g.domainRecognition R D) W
    (g.domainRecognition_admissible R D W hD)
  let J := g.recognitionSourceIndex (g.domainRecognition R E) W'
    (g.domainRecognition_admissible R E W' hE)
  have hF : g.baseMap '' (R.chart '' F.locus) ⊆ W.locus :=
    (image_mono (image_mono r.subset)).trans hD
  let L := g.recognitionSourceIndex (g.domainRecognition R F) W
    (g.domainRecognition_admissible R F W hF)
  have hLI : range (g.recognitionSource.atlas.chart L) ⊆
      range (g.recognitionSource.atlas.chart I) :=
    (g.domainRecognition R F).range_chart.subset.trans
      ((image_mono r.subset).trans (g.domainRecognition R D).range_chart.symm.subset)
  have hLJ : range (g.recognitionSource.atlas.chart L) ⊆
      range (g.recognitionSource.atlas.chart J) :=
    (g.domainRecognition R F).range_chart.subset.trans
      ((image_mono s.subset).trans (g.domainRecognition R E).range_chart.symm.subset)
  have hr : (g.domainRecognitionEquiv R F).symm.toBoundedAlgHom.comp
      (g.recognitionSource.atlas.restriction L I hLI) =
        r.restriction.comp (g.domainRecognitionEquiv R D).symm.toBoundedAlgHom := by
    have hn := A.atlas.fullRecognitionLocalDomainAlgebraEquiv_naturality
      ((LocalDomain.sameChartFunctor A.atlas.fullRecognitionAtlas R).map r)
    apply BoundedAlgHom.ext
    intro x
    have he := congrArg
      (fun z => (g.domainRecognitionEquiv R F).symm
        (z ((g.domainRecognitionEquiv R D).symm x))) hn
    change (g.domainRecognitionEquiv R F).symm
      ((g.domainRecognitionEquiv R F) (r.restriction ((g.domainRecognitionEquiv R D).symm x))) =
      (g.domainRecognitionEquiv R F).symm
        ((g.recognitionSource.atlas.restriction L I hLI)
          ((g.domainRecognitionEquiv R D) ((g.domainRecognitionEquiv R D).symm x))) at he
    change (g.domainRecognitionEquiv R F).symm
      ((g.recognitionSource.atlas.restriction L I hLI) x) =
      r.restriction ((g.domainRecognitionEquiv R D).symm x)
    exact (congrArg (fun z => (g.domainRecognitionEquiv R F).symm
      ((g.recognitionSource.atlas.restriction L I hLI) z))
        ((g.domainRecognitionEquiv R D).apply_symm_apply x)).symm.trans
          (he.symm.trans ((g.domainRecognitionEquiv R F).symm_apply_apply _))
  have hs : (g.domainRecognitionEquiv R F).symm.toBoundedAlgHom.comp
      (g.recognitionSource.atlas.restriction L J hLJ) =
        s.restriction.comp (g.domainRecognitionEquiv R E).symm.toBoundedAlgHom := by
    have hn := A.atlas.fullRecognitionLocalDomainAlgebraEquiv_naturality
      ((LocalDomain.sameChartFunctor A.atlas.fullRecognitionAtlas R).map s)
    apply BoundedAlgHom.ext
    intro x
    have he := congrArg
      (fun z => (g.domainRecognitionEquiv R F).symm
        (z ((g.domainRecognitionEquiv R E).symm x))) hn
    change (g.domainRecognitionEquiv R F).symm
      ((g.domainRecognitionEquiv R F) (s.restriction ((g.domainRecognitionEquiv R E).symm x))) =
      (g.domainRecognitionEquiv R F).symm
        ((g.recognitionSource.atlas.restriction L J hLJ)
          ((g.domainRecognitionEquiv R E) ((g.domainRecognitionEquiv R E).symm x))) at he
    change (g.domainRecognitionEquiv R F).symm
      ((g.recognitionSource.atlas.restriction L J hLJ) x) =
      s.restriction ((g.domainRecognitionEquiv R E).symm x)
    exact (congrArg (fun z => (g.domainRecognitionEquiv R F).symm
      ((g.recognitionSource.atlas.restriction L J hLJ) z))
        ((g.domainRecognitionEquiv R E).apply_symm_apply x)).symm.trans
          (he.symm.trans ((g.domainRecognitionEquiv R F).symm_apply_apply _))
  have hc := g.recognitionSource.atlas.isMapChartChange_restriction L I J hLI hLJ
    F.algebra (g.domainRecognitionEquiv R F).symm.toBoundedAlgHom
  erw [hr, hs] at hc
  exact hc

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.FiniteOpenBaseChangeModels

open CategoryTheory Set Topology PresentedAffinoidAlgebra IndexedAffinoidAtlas
open FiniteAffinoidAlgebraDescent

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  {f : StrongHom A.saturatedPresentation C.saturatedPresentation}
  {g : StrongHom B.saturatedPresentation C.saturatedPresentation}
  {V : Set A.space} {U : Set C.space} {R : B.atlas.saturatedAtlas.RecognizedSubset}
  (M : FiniteOpenBaseChangeModels f g V U R)

/-- The unchanged geometric overlap algebra is the precise original
base change used by the algebraic descent interface. -/
def modelOverlapComparison (i j : Fin M.rightCover.cover.size) :
    BoundedAlgEquiv K
      (M.descentLocalAlgebras.baseChange j
        (M.descentLocalAlgebras.overlap i j) (M.descentLocalAlgebras.overlapRight i j))
      (M.modelOverlapDomain i j).algebra :=
  AffinoidPushout.rightEqEquiv (M.rightMap j)
    (M.descentLocalAlgebras.overlapRight_restriction i j)

theorem modelOverlapComparison_comp_localMap (i j : Fin M.rightCover.cover.size) :
    (M.modelOverlapComparison i j).toBoundedAlgHom.comp
      (M.descentLocalAlgebras.localMap j
        (M.descentLocalAlgebras.overlap i j) (M.descentLocalAlgebras.overlapRight i j)) =
      (M.modelOverlapDomain i j).baseMap :=
  AffinoidPushout.rightEqEquiv_comp_left (M.rightMap j) _

/-- The complete original intersection coefficient leg of the geometric overlap. -/
def modelOverlapBaseMap (i j : Fin M.rightCover.cover.size) :
    BoundedAlgHom K (M.descentLocalAlgebras.overlap i j).algebra
      (M.modelOverlapDomain i j).algebra :=
  AffinoidPushout.rightMap _ _

theorem modelOverlapComparison_comp_baseMap (i j : Fin M.rightCover.cover.size) :
    (M.modelOverlapComparison i j).toBoundedAlgHom.comp
      (M.descentLocalAlgebras.baseMap j
        (M.descentLocalAlgebras.overlap i j) (M.descentLocalAlgebras.overlapRight i j)) =
      M.modelOverlapBaseMap i j :=
  AffinoidPushout.rightEqEquiv_comp_right (M.rightMap j) _

/-- The actual first restriction of the algebraic matching diagram,
with its codomain identified with the unchanged geometric overlap. -/
def modelOverlapLeft (i j : Fin M.rightCover.cover.size) :
    BoundedAlgHom K (M.algebra i) (M.modelOverlapDomain i j).algebra :=
  (M.modelOverlapComparison i j).toBoundedAlgHom.comp
    (M.algebraDescentData.toPairTransitions.leftRestriction i j)

theorem modelOverlapLeft_comp_right (i j : Fin M.rightCover.cover.size) :
    (M.modelOverlapLeft i j).comp (M.rightMap i) =
      (M.modelOverlapBaseMap i j).comp (restriction (M.descentLocalAlgebras.overlapLeft i j)) := by
  change ((M.modelOverlapComparison i j).toBoundedAlgHom.comp
    ((M.descentPairTransitions.equiv i j).toBoundedAlgHom.comp
      (M.descentLocalAlgebras.localMap i _ _))).comp (M.rightMap i) = _
  rw [BoundedAlgHom.comp_assoc, BoundedAlgHom.comp_assoc,
    M.descentLocalAlgebras.condition, ← BoundedAlgHom.comp_assoc
      (M.descentPairTransitions.equiv i j).toBoundedAlgHom,
    M.descentPairTransitions.over_base, ← BoundedAlgHom.comp_assoc,
    M.modelOverlapComparison_comp_baseMap]

/-- Pasting the first descent restriction recovers the original entire
left chart change on the direct finite local pushouts. -/
theorem descentLeftRestriction_pasting_left (i j : Fin M.rightCover.cover.size) :
    ((M.descentBaseChangeEquiv j (M.descentLocalAlgebras.overlap i j)
      (M.descentLocalAlgebras.overlapRight i j)).toBoundedAlgHom.comp
        (M.algebraDescentData.toPairTransitions.leftRestriction i j)).comp (M.leftMap i) =
      M.transitionLeft j i
        (Domain.inclusionOfSubset _ _ (M.descentLocalAlgebras.overlapRight i j))
        (Domain.inclusionOfSubset _ _ (M.descentLocalAlgebras.overlapLeft i j)) := by
  let E := M.descentLocalAlgebras.overlap i j
  let hi := M.descentLocalAlgebras.overlapLeft i j
  let hj := M.descentLocalAlgebras.overlapRight i j
  change ((M.descentBaseChangeEquiv j E hj).toBoundedAlgHom.comp
    ((M.descentTransitionEquiv i j E hi hj).toBoundedAlgHom.comp
      (M.descentLocalAlgebras.localMap i E hi))).comp (M.leftMap i) = _
  calc
    _ = (((M.descentBaseChangeEquiv j E hj).toBoundedAlgHom.comp
        (M.descentTransitionEquiv i j E hi hj).toBoundedAlgHom).comp
          (M.descentLocalAlgebras.localMap i E hi)).comp (M.leftMap i) := rfl
    _ = ((M.transitionMap j i (Domain.inclusionOfSubset E _ hj)
        (Domain.inclusionOfSubset E _ hi)).comp
          ((M.descentBaseChangeEquiv i E hi).toBoundedAlgHom.comp
            (M.descentLocalAlgebras.localMap i E hi))).comp (M.leftMap i) :=
      congrArg (fun z => (z.comp (M.descentLocalAlgebras.localMap i E hi)).comp (M.leftMap i))
        (M.descentTransitionEquiv_pasting i j E hi hj)
    _ = (M.transitionMap j i (Domain.inclusionOfSubset E _ hj)
        (Domain.inclusionOfSubset E _ hi)).comp
          (M.restrictedLeftMap i (Domain.inclusionOfSubset E _ hi)) :=
      congrArg (fun z => (M.transitionMap j i (Domain.inclusionOfSubset E _ hj)
        (Domain.inclusionOfSubset E _ hi)).comp z)
          (M.descentBaseChangeEquiv_comp_localMap_left i E hi)
    _ = _ := M.transitionMap_comp_left j i _ _

/-- The first overlap restriction preserves the full left-factor
coefficient chart-change law before any saturated representative is chosen. -/
theorem modelOverlapLeft_isMapChartChange_left (i j : Fin M.rightCover.cover.size) :
    f.recognitionSource.atlas.IsMapChartChange (M.leftIndex j) (M.leftIndex i)
      (M.modelOverlapDomain i j).algebra
      ((M.modelOverlapDomain i j).baseMap.comp (M.leftMap j))
      ((M.modelOverlapLeft i j).comp (M.leftMap i)) := by
  let E := M.descentLocalAlgebras.overlap i j
  let hi := M.descentLocalAlgebras.overlapLeft i j
  let hj := M.descentLocalAlgebras.overlapRight i j
  let e := M.descentBaseChangeEquiv j E hj
  let q := (M.modelOverlapComparison i j).toBoundedAlgHom.comp e.symm.toBoundedAlgHom
  have h := (f.recognitionSource.atlas.changeMapChart_isMapChartChange
    (M.leftIndex j) (M.leftIndex i) (M.restrictedAlgebra j (Domain.inclusionOfSubset E _ hj))
    (M.restrictedLeftMap j (Domain.inclusionOfSubset E _ hj))
    (M.restrictedLeftPoint_mem j i (Domain.inclusionOfSubset E _ hj)
      (Domain.inclusionOfSubset E _ hi))).comp f.recognitionSource.atlas q
  change f.recognitionSource.atlas.IsMapChartChange (M.leftIndex j) (M.leftIndex i)
    (M.modelOverlapDomain i j).algebra
    (q.comp (M.restrictedLeftMap j (Domain.inclusionOfSubset E _ hj)))
    (q.comp (M.transitionLeft j i (Domain.inclusionOfSubset E _ hj)
      (Domain.inclusionOfSubset E _ hi))) at h
  have h₁ : q.comp (M.restrictedLeftMap j (Domain.inclusionOfSubset E _ hj)) =
      (M.modelOverlapDomain i j).baseMap.comp (M.leftMap j) := by
    apply BoundedAlgHom.ext
    intro x
    have he := congrArg (fun z => z x) (M.descentBaseChangeEquiv_comp_localMap_left j E hj)
    change q (M.restrictedLeftMap j (Domain.inclusionOfSubset E _ hj) x) = _
    rw [← he]
    change (M.modelOverlapComparison i j)
      (e.symm (e ((M.descentLocalAlgebras.localMap j E hj) ((M.leftMap j) x)))) = _
    rw [e.symm_apply_apply]
    exact congrArg (fun z => z ((M.leftMap j) x))
      (M.modelOverlapComparison_comp_localMap i j)
  have h₂ : q.comp (M.transitionLeft j i (Domain.inclusionOfSubset E _ hj)
      (Domain.inclusionOfSubset E _ hi)) =
        (M.modelOverlapLeft i j).comp (M.leftMap i) := by
    apply BoundedAlgHom.ext
    intro x
    have he := congrArg (fun z => z x) (M.descentLeftRestriction_pasting_left i j)
    change q (M.transitionLeft j i (Domain.inclusionOfSubset E _ hj)
      (Domain.inclusionOfSubset E _ hi) x) = _
    rw [← he]
    change (M.modelOverlapComparison i j)
      (e.symm (e ((M.algebraDescentData.toPairTransitions.leftRestriction i j)
        ((M.leftMap i) x)))) = _
    rw [e.symm_apply_apply]
    rfl
  erw [h₁, h₂] at h
  exact h

/-- The same first overlap restriction also retains the complete
right-factor chart change through the literal original intersection. -/
theorem modelOverlapLeft_isMapChartChange_right (i j : Fin M.rightCover.cover.size) :
    g.recognitionSource.atlas.IsMapChartChange (M.pairIndex j).1.2 (M.pairIndex i).1.2
      (M.modelOverlapDomain i j).algebra
      (((M.modelOverlapDomain i j).baseMap.comp (M.rightMap j)).comp
        (M.rightRecognitionEquiv j).symm.toBoundedAlgHom)
      (((M.modelOverlapLeft i j).comp (M.rightMap i)).comp
        (M.rightRecognitionEquiv i).symm.toBoundedAlgHom) := by
  let E := M.descentLocalAlgebras.overlap i j
  let r := (M.rightCover.cover.obj i).interRight (M.rightCover.cover.obj j)
  let s := (M.rightCover.cover.obj i).interLeft (M.rightCover.cover.obj j)
  have h := (g.domainRecognition_overlap_source_change R
    (M.rightCover.cover.obj j) (M.rightCover.cover.obj i) E r s
    (M.rightCover.target j) (M.rightCover.target i)
    (M.rightCover.image_subset_target j) (M.rightCover.image_subset_target i)).comp
      g.recognitionSource.atlas (M.modelOverlapBaseMap i j)
  have hR : (M.modelOverlapDomain i j).baseMap.comp (M.rightMap j) =
      (M.modelOverlapBaseMap i j).comp r.restriction := AffinoidPushout.condition _ _
  have hL : (M.modelOverlapLeft i j).comp (M.rightMap i) =
      (M.modelOverlapBaseMap i j).comp s.restriction :=
    (M.modelOverlapLeft_comp_right i j).trans
      (congrArg (fun z => (M.modelOverlapBaseMap i j).comp z)
        (M.descentLocalAlgebras.overlapLeft_restriction i j))
  change g.recognitionSource.atlas.IsMapChartChange (M.pairIndex j).1.2 (M.pairIndex i).1.2
    (M.modelOverlapDomain i j).algebra
    (((M.modelOverlapBaseMap i j).comp r.restriction).comp
      (M.rightRecognitionEquiv j).symm.toBoundedAlgHom)
    (((M.modelOverlapBaseMap i j).comp s.restriction).comp
      (M.rightRecognitionEquiv i).symm.toBoundedAlgHom) at h
  erw [← hR, ← hL] at h
  exact h

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.FiniteOpenBaseChangeModels
