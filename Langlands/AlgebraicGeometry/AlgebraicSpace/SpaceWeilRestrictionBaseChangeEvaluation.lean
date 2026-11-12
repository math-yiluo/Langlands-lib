import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionEvaluation
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionTensorBaseChange

/-! # Original counit evaluation under cartesian change of base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (A B C D R E : Type u)
  [CommRing A] [CommRing B] [CommRing C] [CommRing D] [CommRing R] [CommRing E]
  [Algebra A B] [Algebra A C] [Algebra B D] [Algebra C D]
  [Algebra A R] [Algebra C R] [IsScalarTower A C R]
  [Algebra B E] [Algebra D E] [IsScalarTower B D E]
  (hcart : IsPullback (Spec.algebraMap B D) (Spec.algebraMap C D)
    (Spec.algebraMap A B) (Spec.algebraMap A C))
  (f : R →+* E)
  (hf : f.comp (algebraMap A R) = (algebraMap B E).comp (algebraMap A B))
  (hf' : f.comp (algebraMap C R) = (algebraMap D E).comp (algebraMap C D))

/-- The cartesian Weil comparison intertwines both original coefficient evaluation tests. -/
theorem weilRestrictionBaseChangeEvaluationTest :
    (ringTestRestrictScalarsIso B D E).inv ≫
      (Over.map (Spec.algebraMap B D)).map (weilRestrictionEvaluationTest C D R E f hf') ≫
      (WeilRestrictionBaseChange.testIso hcart (ringTest C R)).hom =
    weilRestrictionEvaluationTest A B R E f hf ≫
      (Over.pullback (Spec.algebraMap A B)).map (ringTestRestrictScalarsIso A C R).inv := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc]
    change _ ≫ _ ≫ (WeilRestrictionBaseChange.testIso hcart (ringTest C R)).hom.left ≫
      pullback.fst ((ringTest C R).hom ≫ Spec.algebraMap A C)
        (Spec.algebraMap A B) = _
    rw [WeilRestrictionBaseChange.testIso_hom_fst]
    simp only [Over.map_map_left, ringTestRestrictScalarsIso_inv_left,
      Category.id_comp, Over.pullback_map_left, pullback.lift_fst]
    simp only [Category.comp_id]
    change (weilRestrictionEvaluationTest C D R E f hf').left ≫
        pullback.fst (Spec.algebraMap C R) (Spec.algebraMap C D) =
      (weilRestrictionEvaluationTest A B R E f hf).left ≫
        pullback.fst (Spec.algebraMap A R) (Spec.algebraMap A B)
    rw [weilRestrictionEvaluationTest_fst, weilRestrictionEvaluationTest_fst]
  · exact (Over.w ((ringTestRestrictScalarsIso B D E).inv ≫
      (Over.map (Spec.algebraMap B D)).map (weilRestrictionEvaluationTest C D R E f hf') ≫
      (WeilRestrictionBaseChange.testIso hcart (ringTest C R)).hom)).trans
      (Over.w (weilRestrictionEvaluationTest A B R E f hf ≫
        (Over.pullback (Spec.algebraMap A B)).map
          (ringTestRestrictScalarsIso A C R).inv)).symm

variable (X : AlgebraicSpace (Spec (CommRingCat.of B)))
  (h : IsAlgebraicSpace _ ((ringWeilRestriction A B).obj X.toSheaf))

/-- Evaluate after the actual cartesian Weil comparison, retaining the original upper base. -/
def baseChangedSpaceWeilEvaluation
    (y : RingPoints C (baseChange (Spec.algebraMap A C)
      (ringWeilRestrictionSpace A B X h)) R) : RingPoints B X E :=
  baseChangeRingPointsEquiv B D E X
    (spaceWeilRestrictionEvaluation C D R E f hf'
      (baseChange (Spec.algebraMap B D) X)
      (isAlgebraicSpace_weilRestriction_baseChange hcart X h)
      (RingPoints.map (weilRestrictionBaseChangeIso hcart X h).hom y))

/-- The original counit evaluation commutes with the actual cartesian Weil isomorphism
on every compatible coefficient algebra. -/
theorem spaceWeilRestrictionEvaluation_baseChange
    (y : RingPoints C (baseChange (Spec.algebraMap A C)
      (ringWeilRestrictionSpace A B X h)) R) :
    baseChangeRingPointsEquiv B D E X
      (spaceWeilRestrictionEvaluation C D R E f hf'
        (baseChange (Spec.algebraMap B D) X)
        (isAlgebraicSpace_weilRestriction_baseChange hcart X h)
        (RingPoints.map (weilRestrictionBaseChangeIso hcart X h).hom y)) =
      spaceWeilRestrictionEvaluation A B R E f hf X h
        (baseChangeRingPointsEquiv A C R (ringWeilRestrictionSpace A B X h) y) := by
  change X.pullback (ringTestRestrictScalarsIso B D E).inv
      (X.pullback ((Over.map (Spec.algebraMap B D)).map
        (weilRestrictionEvaluationTest C D R E f hf'))
        (X.pullback (WeilRestrictionBaseChange.testIso hcart (ringTest C R)).hom y)) =
    X.pullback (weilRestrictionEvaluationTest A B R E f hf)
      (X.pullback ((Over.pullback (Spec.algebraMap A B)).map
        (ringTestRestrictScalarsIso A C R).inv) y)
  have hx := congrArg (fun g => X.presheaf.map g.op)
    (weilRestrictionBaseChangeEvaluationTest A B C D R E hcart f hf hf')
  have hy := ConcreteCategory.congr_hom hx y
  simpa only [op_comp, Functor.map_comp, types_comp_apply] using hy

end Langlands.AlgebraicGeometry.AlgebraicSpace
