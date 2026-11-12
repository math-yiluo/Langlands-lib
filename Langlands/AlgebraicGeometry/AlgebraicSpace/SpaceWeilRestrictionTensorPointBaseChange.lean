import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionTensorPoints

/-! # Cartesian base change on tensor Weil points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

section BaseTest

variable (C D : Type u) [CommRing C] [CommRing D] [Algebra C D]

@[reassoc (attr := simp)]
theorem weilRestrictionBaseTestIso_hom_fst :
    (weilRestrictionBaseTestIso C D).hom.left ≫
      pullback.fst (Spec.algebraMap C C) (Spec.algebraMap C D) =
        Spec.algebraMap C D := by
  change ((ringTestMap D (Algebra.TensorProduct.rid C D D).toAlgHom).left ≫
    (ringBaseChangeSpectrumIso C D C).inv.left) ≫ _ = _
  rw [Category.assoc, ringBaseChangeSpectrumIso_inv_fst, ringTestMap_left,
    ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun c => by simp [Algebra.smul_def])

/-- The base-point equivalence is evaluation on the canonical base test
isomorphism. -/
theorem ringWeilRestrictionBasePointsEquiv_apply
    (X : AlgebraicSpace (Spec (CommRingCat.of D)))
    (h : IsAlgebraicSpace _ ((ringWeilRestriction C D).obj X.toSheaf))
    (x : RingPoints C (ringWeilRestrictionSpace C D X h) C) :
    ringWeilRestrictionBasePointsEquiv C D X h x =
      X.pullback (weilRestrictionBaseTestIso C D).hom x := by
  change X.pullback (weilRestrictionTensorUnitTestIso C D).hom
    (X.pullback (ringBaseChangeSpectrumIso C D C).inv x) = _
  rw [← pullback_comp]
  rfl

end BaseTest

section Tensor

variable (R B C D : Type u) [CommRing R] [CommRing B] [CommRing C] [CommRing D]
  [Algebra R B] [Algebra R C] [Algebra C D] [Algebra B D]
  (e : C ⊗[R] B ≃ₐ[C] D)
  (he : ∀ b : B, e (1 ⊗ₜ[R] b) = algebraMap B D b)

/-- The cartesian comparison, evaluated on the base-point test, retains
both original coefficient maps. -/
theorem weilRestrictionTensorBasePointTestMap :
    (ringTestRestrictScalarsIso B D D).inv ≫
      (Over.map (Spec.algebraMap B D)).map (weilRestrictionBaseTestIso C D).hom ≫
      (WeilRestrictionBaseChange.testIso
        (isPullback_weilRestrictionTensor R B C D e he) (ringTest C C)).hom =
    weilRestrictionTensorPointTestMap R B C D e he ≫
      (Over.pullback (Spec.algebraMap R B)).map
        (ringTestRestrictScalarsIso R C C).inv := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc]
    change _ ≫ _ ≫
      (WeilRestrictionBaseChange.testIso
        (isPullback_weilRestrictionTensor R B C D e he) (ringTest C C)).hom.left ≫
      pullback.fst ((ringTest C C).hom ≫ Spec.algebraMap R C)
        (Spec.algebraMap R B) = _
    rw [WeilRestrictionBaseChange.testIso_hom_fst]
    simp only [Over.map_map_left, ringTestRestrictScalarsIso_inv_left,
      Category.id_comp]
    simp only [Over.pullback_map_left, pullback.lift_fst]
    change (weilRestrictionBaseTestIso C D).hom.left ≫
        pullback.fst (Spec.algebraMap C C) (Spec.algebraMap C D) =
      (weilRestrictionTensorPointTestMap R B C D e he).left ≫
        pullback.fst (Spec.algebraMap R C) (Spec.algebraMap R B)
    rw [weilRestrictionBaseTestIso_hom_fst, weilRestrictionTensorPointTestMap_fst]
  · exact (Over.w ((ringTestRestrictScalarsIso B D D).inv ≫
      (Over.map (Spec.algebraMap B D)).map (weilRestrictionBaseTestIso C D).hom ≫
      (WeilRestrictionBaseChange.testIso
        (isPullback_weilRestrictionTensor R B C D e he) (ringTest C C)).hom)).trans
      (Over.w (weilRestrictionTensorPointTestMap R B C D e he ≫
        (Over.pullback (Spec.algebraMap R B)).map
          (ringTestRestrictScalarsIso R C C).inv)).symm

variable (X : AlgebraicSpace (Spec (CommRingCat.of B)))
  (h : IsAlgebraicSpace _ ((ringWeilRestriction R B).obj X.toSheaf))

/-- The cartesian space isomorphism induces the original-coefficient
tensor equivalence on points. -/
theorem ringWeilRestrictionTensorBaseChangeIso_points
    (y : RingPoints C
      (baseChange (Spec.algebraMap R C) (ringWeilRestrictionSpace R B X h)) C) :
    baseChangeRingPointsEquiv B D D X
      (ringWeilRestrictionBasePointsEquiv C D (baseChange (Spec.algebraMap B D) X)
        (isAlgebraicSpace_ringWeilRestriction_tensor R B C D e he X h)
        (RingPoints.map (ringWeilRestrictionTensorBaseChangeIso R B C D e he X h).hom y)) =
    ringWeilRestrictionTensorPointsEquiv R B C D e he X h
      (baseChangeRingPointsEquiv R C C (ringWeilRestrictionSpace R B X h) y) := by
  rw [ringWeilRestrictionTensorPointsEquiv_apply,
    ringWeilRestrictionBasePointsEquiv_apply]
  change X.pullback (ringTestRestrictScalarsIso B D D).inv
      (X.pullback ((Over.map (Spec.algebraMap B D)).map
        (weilRestrictionBaseTestIso C D).hom)
        (X.pullback (WeilRestrictionBaseChange.testIso
          (isPullback_weilRestrictionTensor R B C D e he) (ringTest C C)).hom y)) =
    X.pullback (weilRestrictionTensorPointTestMap R B C D e he)
      (X.pullback ((Over.pullback (Spec.algebraMap R B)).map
        (ringTestRestrictScalarsIso R C C).inv) y)
  have hx := congrArg (fun f => X.presheaf.map f.op)
    (weilRestrictionTensorBasePointTestMap R B C D e he)
  have hy := ConcreteCategory.congr_hom hx y
  simpa only [op_comp, Functor.map_comp, types_comp_apply] using hy

/-- The tensor point equivalence on the base-changed Weil space, with
the original upper coefficient structure. -/
def ringWeilRestrictionTensorBaseChangePointsEquiv :
    RingPoints C
      (baseChange (Spec.algebraMap R C) (ringWeilRestrictionSpace R B X h)) C ≃
        RingPoints B X D :=
  (baseChangeRingPointsEquiv R C C (ringWeilRestrictionSpace R B X h)).trans
    (ringWeilRestrictionTensorPointsEquiv R B C D e he X h)

/-- This equivalence is also the cartesian space comparison followed by
the local Weil base-point and upper base-change identifications. -/
theorem ringWeilRestrictionTensorBaseChangePointsEquiv_apply
    (y : RingPoints C
      (baseChange (Spec.algebraMap R C) (ringWeilRestrictionSpace R B X h)) C) :
    ringWeilRestrictionTensorBaseChangePointsEquiv R B C D e he X h y =
      baseChangeRingPointsEquiv B D D X
        (ringWeilRestrictionBasePointsEquiv C D (baseChange (Spec.algebraMap B D) X)
          (isAlgebraicSpace_ringWeilRestriction_tensor R B C D e he X h)
          (RingPoints.map (ringWeilRestrictionTensorBaseChangeIso R B C D e he X h).hom y)) :=
  (ringWeilRestrictionTensorBaseChangeIso_points R B C D e he X h y).symm

end Tensor

end Langlands.AlgebraicGeometry.AlgebraicSpace
