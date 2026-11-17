import Langlands.Geometry.Analytic.FiniteOpenBaseChangeTransitions
import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidPushoutPasting

/-! # Restriction and pasting of complete finite-open base-change models -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.FiniteOpenBaseChangeModels

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  {f : StrongHom A.saturatedPresentation C.saturatedPresentation}
  {g : StrongHom B.saturatedPresentation C.saturatedPresentation}
  {V : Set A.space} {U : Set C.space} {R : B.atlas.saturatedAtlas.RecognizedSubset}
  (M : FiniteOpenBaseChangeModels f g V U R)

/-- The full closed-quotient base change of a local model is boundedly
equivalent to the direct model over the original smaller domain. -/
def baseChangeEquiv (i : Fin M.rightCover.cover.size) {E : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) :
    BoundedAlgEquiv K (AffinoidPushout.algebra (M.rightMap i) r.restriction)
      (M.restrictedAlgebra i r) :=
  AffinoidPushout.pastingEquiv (M.leftBase i) (M.rightCover.canonicalPullback i) r.restriction

theorem baseChangeEquiv_comp_right (i : Fin M.rightCover.cover.size) {E : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) :
    (M.baseChangeEquiv i r).toBoundedAlgHom.comp (AffinoidPushout.rightMap (M.rightMap i) r.restriction) =
      M.restrictedRightMap i r :=
  AffinoidPushout.pastingEquiv_comp_right _ _ _

theorem baseChangeEquiv_comp_left (i : Fin M.rightCover.cover.size) {E : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) :
    (M.baseChangeEquiv i r).toBoundedAlgHom.comp
      ((AffinoidPushout.leftMap (M.rightMap i) r.restriction).comp (M.leftMap i)) =
        M.restrictedLeftMap i r :=
  AffinoidPushout.pastingEquiv_comp_left _ _ _

theorem baseChangeEquiv_symm_comp_right (i : Fin M.rightCover.cover.size) {E : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) :
    (M.baseChangeEquiv i r).symm.toBoundedAlgHom.comp (M.restrictedRightMap i r) =
      AffinoidPushout.rightMap (M.rightMap i) r.restriction :=
  AffinoidPushout.directToPasting_comp_right _ _ _

theorem baseChangeEquiv_symm_comp_left (i : Fin M.rightCover.cover.size) {E : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) :
    (M.baseChangeEquiv i r).symm.toBoundedAlgHom.comp (M.restrictedLeftMap i r) =
      (AffinoidPushout.leftMap (M.rightMap i) r.restriction).comp (M.leftMap i) :=
  AffinoidPushout.directToPasting_comp_left _ _ _

private theorem restrictionMap_condition
    (i : Fin M.rightCover.cover.size) {E F : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) (s : F ⟶ M.rightCover.cover.obj i) (q : F ⟶ E) :
    (M.restrictedLeftMap i s).comp (M.leftBase i) =
      ((M.restrictedRightMap i s).comp q.restriction).comp
        (r.restriction.comp (M.rightCover.canonicalPullback i)) := by
  have h : q.restriction.comp r.restriction = s.restriction :=
    congrArg Domain.Inclusion.restriction
      (@Subsingleton.elim (Domain.Inclusion F (M.rightCover.cover.obj i)) inferInstance (q ≫ r) s)
  rw [BoundedAlgHom.comp_assoc, ← BoundedAlgHom.comp_assoc q.restriction r.restriction, h]
  exact AffinoidPushout.condition _ _

/-- The canonical actual bounded restriction under any further full-domain
arrow, retaining the entire left map and the original coefficient map. -/
def restrictionMap (i : Fin M.rightCover.cover.size) {E F : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) (s : F ⟶ M.rightCover.cover.obj i) (q : F ⟶ E) :
    BoundedAlgHom K (M.restrictedAlgebra i r) (M.restrictedAlgebra i s) :=
  AffinoidPushout.lift (M.leftBase i) (r.restriction.comp (M.rightCover.canonicalPullback i)) _
    (M.restrictedLeftMap i s) ((M.restrictedRightMap i s).comp q.restriction)
    (M.restrictionMap_condition i r s q)

theorem restrictionMap_comp_left (i : Fin M.rightCover.cover.size) {E F : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) (s : F ⟶ M.rightCover.cover.obj i) (q : F ⟶ E) :
    (M.restrictionMap i r s q).comp (M.restrictedLeftMap i r) = M.restrictedLeftMap i s :=
  AffinoidPushout.lift_comp_leftMap _ _ _ _ _ _

theorem restrictionMap_comp_right (i : Fin M.rightCover.cover.size) {E F : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) (s : F ⟶ M.rightCover.cover.obj i) (q : F ⟶ E) :
    (M.restrictionMap i r s q).comp (M.restrictedRightMap i r) =
      (M.restrictedRightMap i s).comp q.restriction :=
  AffinoidPushout.lift_comp_rightMap _ _ _ _ _ _

theorem restrictionMap_self (i : Fin M.rightCover.cover.size) {E : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) :
    M.restrictionMap i r r (𝟙 E) = BoundedAlgHom.id K (M.restrictedAlgebra i r) := by
  apply AffinoidPushout.hom_ext (M.leftBase i) (r.restriction.comp (M.rightCover.canonicalPullback i))
  · change (M.restrictionMap i r r (𝟙 E)).comp (M.restrictedLeftMap i r) =
      (BoundedAlgHom.id K _).comp (M.restrictedLeftMap i r)
    rw [M.restrictionMap_comp_left, BoundedAlgHom.id_comp]
  · change (M.restrictionMap i r r (𝟙 E)).comp (M.restrictedRightMap i r) =
      (BoundedAlgHom.id K _).comp (M.restrictedRightMap i r)
    rw [M.restrictionMap_comp_right, Domain.Inclusion.restriction_id,
      BoundedAlgHom.comp_id, BoundedAlgHom.id_comp]

theorem restrictionMap_comp (i : Fin M.rightCover.cover.size) {E F G : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) (s : F ⟶ M.rightCover.cover.obj i)
    (t : G ⟶ M.rightCover.cover.obj i) (q : F ⟶ E) (p : G ⟶ F) :
    (M.restrictionMap i s t p).comp (M.restrictionMap i r s q) =
      M.restrictionMap i r t (p ≫ q) := by
  apply AffinoidPushout.hom_ext (M.leftBase i) (r.restriction.comp (M.rightCover.canonicalPullback i))
  · change ((M.restrictionMap i s t p).comp (M.restrictionMap i r s q)).comp (M.restrictedLeftMap i r) =
      (M.restrictionMap i r t (p ≫ q)).comp (M.restrictedLeftMap i r)
    rw [BoundedAlgHom.comp_assoc, M.restrictionMap_comp_left,
      M.restrictionMap_comp_left, M.restrictionMap_comp_left]
  · change ((M.restrictionMap i s t p).comp (M.restrictionMap i r s q)).comp (M.restrictedRightMap i r) =
      (M.restrictionMap i r t (p ≫ q)).comp (M.restrictedRightMap i r)
    rw [BoundedAlgHom.comp_assoc, M.restrictionMap_comp_right,
      ← BoundedAlgHom.comp_assoc, M.restrictionMap_comp_right, M.restrictionMap_comp_right]
    rfl

/-- The entire overlap transition commutes with every further actual
full-domain restriction. This proves the refinement law, not just its
effect on spectra or base coefficients. -/
theorem transitionMap_naturality
    (i j : Fin M.rightCover.cover.size) {E F : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) (s : E ⟶ M.rightCover.cover.obj j)
    (r' : F ⟶ M.rightCover.cover.obj i) (s' : F ⟶ M.rightCover.cover.obj j) (q : F ⟶ E) :
    (M.restrictionMap i r r' q).comp (M.transitionMap i j r s) =
      (M.transitionMap i j r' s').comp (M.restrictionMap j s s' q) := by
  apply AffinoidPushout.hom_ext (M.leftBase j) (s.restriction.comp (M.rightCover.canonicalPullback j))
  · change ((M.restrictionMap i r r' q).comp (M.transitionMap i j r s)).comp (M.restrictedLeftMap j s) =
      ((M.transitionMap i j r' s').comp (M.restrictionMap j s s' q)).comp (M.restrictedLeftMap j s)
    rw [BoundedAlgHom.comp_assoc, BoundedAlgHom.comp_assoc, M.transitionMap_comp_left,
      M.restrictionMap_comp_left, M.transitionMap_comp_left]
    have hc := (f.recognitionSource.atlas.changeMapChart_isMapChartChange
      (M.leftIndex i) (M.leftIndex j) (M.restrictedAlgebra i r) (M.restrictedLeftMap i r)
      (M.restrictedLeftPoint_mem i j r s)).comp
        f.recognitionSource.atlas (M.restrictionMap i r r' q)
    change f.recognitionSource.atlas.IsMapChartChange (M.leftIndex i) (M.leftIndex j)
      (M.restrictedAlgebra i r') ((M.restrictionMap i r r' q).comp (M.restrictedLeftMap i r))
      ((M.restrictionMap i r r' q).comp (M.transitionLeft i j r s)) at hc
    erw [M.restrictionMap_comp_left] at hc
    exact f.recognitionSource.atlas.eq_changeMapChart (M.leftIndex i) (M.leftIndex j)
      (M.restrictedAlgebra i r') (M.restrictedLeftMap i r')
      (M.restrictedLeftPoint_mem i j r' s')
      ((M.restrictionMap i r r' q).comp (M.transitionLeft i j r s)) hc
  · change ((M.restrictionMap i r r' q).comp (M.transitionMap i j r s)).comp (M.restrictedRightMap j s) =
      ((M.transitionMap i j r' s').comp (M.restrictionMap j s s' q)).comp (M.restrictedRightMap j s)
    rw [BoundedAlgHom.comp_assoc, BoundedAlgHom.comp_assoc, M.transitionMap_comp_right,
      M.restrictionMap_comp_right, M.restrictionMap_comp_right,
      ← BoundedAlgHom.comp_assoc, M.transitionMap_comp_right]

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.FiniteOpenBaseChangeModels
