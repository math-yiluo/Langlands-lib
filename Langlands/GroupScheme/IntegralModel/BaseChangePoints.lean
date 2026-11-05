import Langlands.GroupScheme.IntegralModel.BaseChange
import Langlands.GroupScheme.IntegralModel.GenericCoordinates
import Langlands.GroupScheme.IntegralModel.CoefficientPoints

/-! # Integral-model base change on arbitrary coefficient points -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

open Langlands.AlgebraicGeometry.PointTopology

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]

/-- Sections of the extended model are actual A-valued points of the original model. -/
def baseChangeSectionsEquiv :
    (M.baseChange A L).integralSections ≃ RingPoint R M.group.X A :=
  (rationalPointEquiv A (ringBaseChange R A M.group.X)).trans
    (ringPointBaseChangeEquiv R A A M.group.X).symm

theorem baseChangeSectionsEquiv_left (s : (M.baseChange A L).integralSections) :
    (M.baseChangeSectionsEquiv A L s).left =
      s.left ≫ pullback.fst M.group.X.hom (Spec.algebraMap R A) := by
  change ((ringPointBaseChangeEquiv R A A M.group.X).symm
    (rationalPointEquiv A (ringBaseChange R A M.group.X) s)).left = _
  rw [ringPointBaseChangeEquiv_symm_left]
  exact congrArg (fun f => f ≫ pullback.fst M.group.X.hom (Spec.algebraMap R A))
    (rationalPointEquiv_left A (ringBaseChange R A M.group.X) s)

set_option maxHeartbeats 800000 in
/-- Arbitrary local sections have the original-model generic point obtained by
coefficient change, using the specified generic-fibre comparison. -/
theorem genericModelPointEquiv_coefficientPointMap
    (s : (M.baseChange A L).integralSections) :
    M.genericModelPointEquiv L ((M.baseChange A L).coefficientPointMap K L s) =
      (M.baseChangeSectionsEquiv A L s).changeRing
        (IsScalarTower.toAlgHom R A L) := by
  apply Over.OverMorphism.ext
  rw [genericModelPointEquiv_left, coefficientPointMap_left]
  rw [← baseChangeSectionHom_left (Spec.algebraMap A L) (M.baseChange A L).group s]
  simp only [Category.assoc]
  change (baseChangeSectionHom (Spec.algebraMap A L)
      ((Langlands.GroupScheme.baseChange (Spec.algebraMap R A)).obj M.group) s).left ≫
        (M.baseChangeGenericIso A L).hom.hom.hom.left ≫
      pullback.fst G.X.hom (Spec.algebraMap K L) ≫
        M.genericIso.inv.hom.hom.left ≫
          pullback.fst M.group.X.hom (Spec.algebraMap R K) = _
  rw [baseChangeGenericIso_hom_fst]
  rw [← Category.assoc]
  have hs := baseChangeSectionHom_fst (Spec.algebraMap A L)
    ((Langlands.GroupScheme.baseChange (Spec.algebraMap R A)).obj M.group) s
  refine (congrArg (fun f =>
    f ≫ pullback.fst M.group.X.hom (Spec.algebraMap R A)) hs).trans ?_
  simp only [Category.assoc]
  change (Spec.algebraMap A L) ≫ s.left ≫
      pullback.fst M.group.X.hom (Spec.algebraMap R A) =
    (Spec.algebraMap A L) ≫ (M.baseChangeSectionsEquiv A L s).left
  rw [baseChangeSectionsEquiv_left]

/-- The local integral image is characterized by extension of the actual
original-model generic point to the local integral algebra. -/
theorem mem_baseChange_coefficientIntegralPoints_iff
    (p : G.affinePoints (CommAlgCat.of K L)) :
    p ∈ (M.baseChange A L).coefficientIntegralPoints K L ↔
      M.genericModelPointEquiv L p ∈ Set.range
        (RingPoint.changeRing (X := M.group.X) (IsScalarTower.toAlgHom R A L)) := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨M.baseChangeSectionsEquiv A L s,
      (M.genericModelPointEquiv_coefficientPointMap A L s).symm⟩
  · rintro ⟨q, hq⟩
    refine ⟨(M.baseChangeSectionsEquiv A L).symm q, ?_⟩
    apply (M.genericModelPointEquiv L).injective
    rw [genericModelPointEquiv_coefficientPointMap, Equiv.apply_symm_apply]
    exact hq

/-- For an integral coefficient subalgebra, the image criterion is evaluation
of every original-model regular function on the specified generic point. -/
theorem mem_baseChange_subalgebra_coefficientIntegralPoints_iff
    (T : Subalgebra R L) [IsFractionRing T L]
    (p : G.affinePoints (CommAlgCat.of K L)) :
    p ∈ (M.baseChange T L).coefficientIntegralPoints K L ↔
      ∀ a : AffineCoordinateRing R M.group.X,
        G.affinePointEvaluation (CommAlgCat.of K L) p (M.genericCoordinate a) ∈ T := by
  let : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
  rw [M.mem_baseChange_coefficientIntegralPoints_iff T L]
  change M.genericModelPointEquiv L p ∈
    Set.range (RingPoint.changeRing (X := M.group.X) T.val) ↔ _
  rw [mem_range_changeRing_subalgebra_iff]
  exact forall_congr' (fun a => by rw [genericModelPointEquiv_evaluation])

/-- The fixed finite original-model test set suffices for the same image criterion. -/
theorem mem_baseChange_subalgebra_coefficientIntegralPoints_iff_testSet
    (T : Subalgebra R L) [IsFractionRing T L]
    (p : G.affinePoints (CommAlgCat.of K L)) :
    p ∈ (M.baseChange T L).coefficientIntegralPoints K L ↔
      ∀ a ∈ integralPointTestSet R M.group.X,
        G.affinePointEvaluation (CommAlgCat.of K L) p (M.genericCoordinate a) ∈ T := by
  let : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
  rw [M.mem_baseChange_coefficientIntegralPoints_iff T L]
  change M.genericModelPointEquiv L p ∈
    Set.range (RingPoint.changeRing (X := M.group.X) T.val) ↔ _
  rw [mem_range_changeRing_subalgebra_iff_testSet]
  exact forall_congr' (fun a =>
    forall_congr' (fun _ => by rw [genericModelPointEquiv_evaluation]))

end Langlands.GroupScheme.IntegralModel
