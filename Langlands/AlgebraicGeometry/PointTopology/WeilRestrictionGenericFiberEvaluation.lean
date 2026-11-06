import Langlands.AlgebraicGeometry.PointTopology.ProjectiveModelWeilGenericFiber
import Langlands.AlgebraicGeometry.PointTopology.WeilRestrictionEvaluation
import Langlands.AlgebraicGeometry.PointTopology.RingPointBaseChange

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open scoped TensorProduct
  Langlands.AlgebraicGeometry.NoetherianApproximation.ProjectiveImmersionRingModelData

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

section Specified

variable (A B C D : Type u) [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra C D] [Algebra B D]
  (e : C ⊗[A] B ≃ₐ[C] D)
  (he : ∀ b : B, e (1 ⊗ₜ[A] b) = algebraMap B D b)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The inverse tensor test identification preserves the original test projection. -/
@[reassoc (attr := simp)]
theorem weilRestrictionTensorBaseChangeTestIso_inv_fst
    (T : Over (Spec (CommRingCat.of C))) :
    (weilRestrictionTensorBaseChangeTestIso A B C T).inv.left ≫
        pullback.fst T.hom
          (pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B)) =
      pullback.fst T.hom (Spec.algebraMap C (C ⊗[A] B)) := by
  apply (cancel_epi (weilRestrictionTensorBaseChangeTestIso A B C T).hom.left).1
  simp [weilRestrictionTensorBaseChangeTestIso]

/-- The inverse tensor test identification preserves the tensor-spectrum projection. -/
@[reassoc (attr := simp)]
theorem weilRestrictionTensorBaseChangeTestIso_inv_snd
    (T : Over (Spec (CommRingCat.of C))) :
    (weilRestrictionTensorBaseChangeTestIso A B C T).inv.left ≫
        pullback.snd T.hom
          (pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B)) =
      pullback.snd T.hom (Spec.algebraMap C (C ⊗[A] B)) ≫
        (pullbackSpecIso A C B).inv := by
  apply (cancel_epi (weilRestrictionTensorBaseChangeTestIso A B C T).hom.left).1
  simp [weilRestrictionTensorBaseChangeTestIso, Category.assoc]

omit [Algebra B D] in
/-- Pasting the three test identifications preserves the lower test projection. -/
@[reassoc (attr := simp)]
theorem specifiedTensorWeilTest_fst
    (T : Over (Spec (CommRingCat.of C))) :
    (weilCoefficientTestIso C (C ⊗[A] B) D e T).hom.left ≫
        (weilRestrictionTensorBaseChangeTestIso A B C T).inv.left ≫
          (weilRestrictionScalarBaseChangeTestIso A B C T).hom.left ≫
            pullback.fst (T.hom ≫ Spec.algebraMap A C) (Spec.algebraMap A B) =
      pullback.fst T.hom (Spec.algebraMap C D) := by
  simp [weilRestrictionScalarBaseChangeTestIso, weilCoefficientTestIso]

include he in
/-- Pasting the three test identifications preserves the original upper base. -/
@[reassoc (attr := simp)]
theorem specifiedTensorWeilTest_snd
    (T : Over (Spec (CommRingCat.of C))) :
    (weilCoefficientTestIso C (C ⊗[A] B) D e T).hom.left ≫
        (weilRestrictionTensorBaseChangeTestIso A B C T).inv.left ≫
          (weilRestrictionScalarBaseChangeTestIso A B C T).hom.left ≫
            pullback.snd (T.hom ≫ Spec.algebraMap A C) (Spec.algebraMap A B) =
      pullback.snd T.hom (Spec.algebraMap C D) ≫ Spec.algebraMap B D := by
  simp [weilRestrictionScalarBaseChangeTestIso, weilCoefficientTestIso,
    Category.assoc, ← specifiedTensorCoefficientSpec_comp A B C D e he]
  rfl

variable (R E : Type u) [CommRing R] [CommRing E]
  [Algebra C R] [Algebra A R] [IsScalarTower A C R]
  [Algebra D E] [Algebra B E] [IsScalarTower B D E]
  (f : R →+* E)
  (hf : f.comp (algebraMap C R) = (algebraMap D E).comp (algebraMap C D))
  (hAB : f.comp (algebraMap A R) = (algebraMap B E).comp (algebraMap A B))

include he in
/-- The pasted test maps are the original integral evaluation test. -/
theorem specifiedTensorWeilTest_eq_evaluation :
    (weilRestrictionEvaluationTest C D R E f hf).left ≫
        (weilCoefficientTestIso C (C ⊗[A] B) D e (ringTest C R)).hom.left ≫
          (weilRestrictionTensorBaseChangeTestIso A B C (ringTest C R)).inv.left ≫
            (weilRestrictionScalarBaseChangeTestIso A B C (ringTest C R)).hom.left ≫
              ((Over.pullback (Spec.algebraMap A B)).map
                (ringTestRestrictScalarsIso A C R).hom).left =
      (weilRestrictionEvaluationTest A B R E f hAB).left := by
  apply pullback.hom_ext
  · simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst]
    simp only [ringTestRestrictScalarsIso_hom_left, Category.comp_id]
    erw [specifiedTensorWeilTest_fst A B C D e (ringTest C R)]
    exact (weilRestrictionEvaluationTest_fst C D R E f hf).trans
      (weilRestrictionEvaluationTest_fst A B R E f hAB).symm
  · simp only [Category.assoc, Over.pullback_map_left, pullback.lift_snd]
    erw [specifiedTensorWeilTest_snd A B C D e he (ringTest C R)]
    erw [← Category.assoc, Over.w (weilRestrictionEvaluationTest C D R E f hf),
      Over.w (weilRestrictionEvaluationTest A B R E f hAB)]
    change Spec.algebraMap D E ≫ Spec.algebraMap B D = Spec.algebraMap B E
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq B D E).symm

variable [Module.Finite A B] [Module.Projective A B]
  (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

/-- The specified tensor comparison retains the original integral counit after projection. -/
theorem affineChartWeilRestrictionSpecifiedTensorComparison_fst
    (T : Over (Spec (CommRingCat.of C)))
    (p : T ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) :
    (affineChartWeilRestrictionSpecifiedTensorComparison A B C D e he Y T p).left ≫
        pullback.fst Y.hom (Spec.algebraMap B D) =
      (weilCoefficientTestIso C (C ⊗[A] B) D e T).hom.left ≫
        (weilRestrictionTensorBaseChangeTestIso A B C T).inv.left ≫
          (weilRestrictionScalarBaseChangeTestIso A B C T).hom.left ≫
            (affineChartWeilRestrictionComparison A B Y _
              (((Over.mapPullbackAdj (Spec.algebraMap A C)).homEquiv T _).symm p)).left := by
  simp [affineChartWeilRestrictionSpecifiedTensorComparison, Category.assoc,
    Over.mapPullbackAdj, affineChartWeilRestrictionTensorBaseChangeComparison,
    weilRestrictionTensorBaseChangeTargetIso]

include he in
/-- Evaluation of the original specified-tensor comparison is base change of integral evaluation. -/
theorem affineChartWeilRestrictionSpecifiedTensorComparison_evaluation
    (p : RingPoint A (affineChartWeilRestriction A B Y) R) :
    weilRestrictionEvaluationTest C D R E f hf ≫
        affineChartWeilRestrictionSpecifiedTensorComparison A B C D e he Y (ringTest C R)
          (ringPointBaseChangeEquiv A C R (affineChartWeilRestriction A B Y) p) =
      ringPointBaseChangeEquiv B D E Y
        (weilRestrictionEvaluation A B R E f hAB Y p) := by
  have hAdj :
      (((Over.mapPullbackAdj (Spec.algebraMap A C)).homEquiv (ringTest C R) _).symm
        (ringPointBaseChangeEquiv A C R (affineChartWeilRestriction A B Y) p)) =
        (ringTestRestrictScalarsIso A C R).hom ≫ p := by
    simp only [ringPointBaseChangeEquiv, Equiv.trans_apply, Iso.homCongr]
    exact ((Over.mapPullbackAdj (Spec.algebraMap A C)).homEquiv (ringTest C R)
      (affineChartWeilRestriction A B Y)).symm_apply_apply _
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc]
    erw [affineChartWeilRestrictionSpecifiedTensorComparison_fst A B C D e he Y]
    rw [hAdj, affineChartWeilRestrictionComparison_natural]
    erw [ringPointBaseChangeEquiv_left_fst B D E Y]
    simpa only [Over.comp_left, Category.assoc, weilRestrictionEvaluation] using
      congrArg (fun z => z ≫ (affineChartWeilRestrictionComparison A B Y (ringTest A R) p).left)
        (specifiedTensorWeilTest_eq_evaluation A B C D e he R E f hf hAB)
  · exact (Over.w (weilRestrictionEvaluationTest C D R E f hf ≫
        affineChartWeilRestrictionSpecifiedTensorComparison A B C D e he Y (ringTest C R)
          (ringPointBaseChangeEquiv A C R (affineChartWeilRestriction A B Y) p))).trans
      (Over.w (ringPointBaseChangeEquiv B D E Y
        (weilRestrictionEvaluation A B R E f hAB Y p))).symm

end Specified

section IntegralGenericFiber

variable (A B K L : Type u)
  [CommRing A] [IsDomain A] [CommRing B] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [FiniteDimensional K L]
  [Algebra A L] [IsScalarTower A K L]
  [Algebra A B] [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
  [Module.Finite A B] [Module.Projective A B]
  (R E : Type u) [CommRing R] [CommRing E]
  [Algebra K R] [Algebra A R] [IsScalarTower A K R]
  [Algebra L E] [Algebra B E] [IsScalarTower B L E]
  (f : R →+* E)
  (hf : f.comp (algebraMap K R) = (algebraMap L E).comp (algebraMap K L))

include hf in
omit [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L]
  [IsIntegralClosure B A L] [Module.Finite A B] [Module.Projective A B] in
/-- Compatibility over the original fields implies compatibility over their integral models. -/
theorem weilRestrictionEvaluation_integralCompatibility :
    f.comp (algebraMap A R) = (algebraMap B E).comp (algebraMap A B) := by
  apply RingHom.ext
  intro a
  have h := congrArg (fun h : K →+* E => h (algebraMap A K a)) hf
  change f (algebraMap K R (algebraMap A K a)) =
    algebraMap L E (algebraMap K L (algebraMap A K a)) at h
  rw [← IsScalarTower.algebraMap_apply A K R,
    ← IsScalarTower.algebraMap_apply A K L,
    IsScalarTower.algebraMap_apply A B L,
    ← IsScalarTower.algebraMap_apply B L E] at h
  exact h

variable {X : Scheme.{u}} {n : ℕ} {j : X ⟶ ProjectiveSpace L n} [IsImmersion j]
  (M : NoetherianApproximation.ProjectiveImmersionRingModelData B L X n j)

local instance originalSchemeLocallyOfFiniteType :
    LocallyOfFiniteType (Over.mk (j ≫ projectiveSpaceToSpec L n)).hom := by
  change LocallyOfFiniteType (j ≫ projectiveSpaceToSpec L n)
  infer_instance

/-- Evaluate on the original field scheme after the constructed Weil generic-fiber identification. -/
def projectiveModelWeilGenericFiberEvaluation
    (p : RingPoint A (affineChartWeilRestriction A B M.asOver) R) :
    RingPoint L (Over.mk (j ≫ projectiveSpaceToSpec L n)) E :=
  weilRestrictionEvaluation K L R E f hf (Over.mk (j ≫ projectiveSpaceToSpec L n))
    (ringPointBaseChangeEquiv A K R (affineChartWeilRestriction A B M.asOver) p ≫
      (projectiveModelWeilGenericFiberIso A B K L M).hom)

/-- The original field counit agrees with integral evaluation followed by the original-model identification. -/
theorem projectiveModelWeilGenericFiberEvaluation_eq_integral
    (p : RingPoint A (affineChartWeilRestriction A B M.asOver) R) :
    projectiveModelWeilGenericFiberEvaluation A B K L R E f hf M p =
      ringPointBaseChangeEquiv B L E M.asOver
        (weilRestrictionEvaluation A B R E f
          (weilRestrictionEvaluation_integralCompatibility A B K L R E f hf) M.asOver p) ≫
        M.genericFiberIso.hom := by
  unfold projectiveModelWeilGenericFiberEvaluation weilRestrictionEvaluation
  rw [projectiveModelWeilGenericFiberIso_comparison, ← Category.assoc]
  rw [affineChartWeilRestrictionSpecifiedTensorComparison_evaluation A B K L
    (Langlands.Global.integralClosureFractionTensorEquiv A B K L)
    (Langlands.Global.integralClosureFractionTensorEquiv_one_tmul A B K L)
    R E f hf (weilRestrictionEvaluation_integralCompatibility A B K L R E f hf) M.asOver]
  rfl

end IntegralGenericFiber

end Langlands.AlgebraicGeometry.PointTopology
