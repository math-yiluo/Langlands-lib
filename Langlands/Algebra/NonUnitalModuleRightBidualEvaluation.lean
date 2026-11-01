import Langlands.Algebra.NonUnitalModuleRightBidualComparison

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleRightBidual

open CategoryTheory MulOpposite NonUnitalModuleDual NonUnitalModuleDualComparison

universe uA uM uN

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]

section Original

variable {M : Type uM} [AddCommGroup M] [NonUnitalModule Aᵐᵒᵖ M]
  (hA : IsIdempotented A) (hM : IsNondegenerate Aᵐᵒᵖ M)

/-- Transport the published opposite-ring evaluation to the actual right bidual. -/
def rightEvaluation :
    letI := rightBidualAction hA hM
    NonUnitalModuleHom Aᵐᵒᵖ M (RightBidual hA hM) :=
  letI := bidualAction hA.op hM
  letI := rightBidualAction hA hM
  (comparisonHom hA hM).comp (evaluation hA.op hM)

theorem rightEvaluation_eq_transport :
    letI := bidualAction hA.op hM
    letI := rightBidualAction hA hM
    rightEvaluation hA hM = (comparisonHom hA hM).comp (evaluation hA.op hM) := rfl

/-- Equality of the entire included full functional after comparison. -/
theorem rightEvaluation_val (m : M) :
    letI := firstDualAction hA hM
    (rightEvaluation hA hM m).val =
      fullComparison hA (isNondegenerate hA.op hM) (fullEvaluation hA.op hM m) := rfl

theorem rightEvaluation_val_coe (m : M) :
    ⇑(rightEvaluation hA hM m).val = fun φ => φ.val m := rfl

@[simp] theorem rightEvaluation_apply (m : M) (φ : Dual hA.op hM) :
    (rightEvaluation hA hM m).val φ = φ.val m := rfl

/-- Every original local fixer is retained, using the published full-evaluation law. -/
theorem rightEvaluation_fixed (m : M) (e : Idempotent Aᵐᵒᵖ)
    (he : (e : Aᵐᵒᵖ) • m = m) :
    letI := rightBidualAction hA hM
    (e : Aᵐᵒᵖ) • rightEvaluation hA hM m = rightEvaluation hA hM m := by
  let _ := bidualAction hA.op hM
  let _ := rightBidualAction hA hM
  have hfix : (e : Aᵐᵒᵖ) • evaluation hA.op hM m = evaluation hA.op hM m := by
    apply Subtype.ext
    exact fullEvaluation_fixed hA.op hM m e he
  exact ((comparisonHom hA hM).map_smul (e : Aᵐᵒᵖ) (evaluation hA.op hM m)).symm.trans
    (congrArg (comparisonHom hA hM) hfix)

theorem rightEvaluation_map_smul (a : Aᵐᵒᵖ) (m : M) :
    letI := rightBidualAction hA hM
    rightEvaluation hA hM (a • m) = a • rightEvaluation hA hM m :=
  letI := rightBidualAction hA hM
  (rightEvaluation hA hM).map_smul a m

/-- The same right map for exactly the recovered original complex modules. -/
def rightEvaluationLinear :
    letI := rightBidualAction hA hM
    letI := NondegenerateScalars.complexModule hA.op hM
    letI := NondegenerateScalars.complexModule hA.op (rightBidual_isNondegenerate hA hM)
    M →ₗ[ℂ] RightBidual hA hM :=
  letI := rightBidualAction hA hM
  NondegenerateScalars.complexToLinearMap hA.op hM (rightBidual_isNondegenerate hA hM)
    (rightEvaluation hA hM)

theorem rightEvaluationLinear_toAddMonoidHom :
    (rightEvaluationLinear hA hM).toAddMonoidHom =
      (rightEvaluation hA hM).toAddMonoidHom := rfl

theorem rightEvaluationLinear_eq_transport :
    letI := bidualAction hA.op hM
    letI := rightBidualAction hA hM
    letI := NondegenerateScalars.complexModule hA.op hM
    letI := NondegenerateScalars.complexModule hA.op (bidual_isNondegenerate hA.op hM)
    letI := NondegenerateScalars.complexModule hA.op (rightBidual_isNondegenerate hA hM)
    rightEvaluationLinear hA hM =
      (comparisonLinear hA hM).toLinearMap.comp (evaluationLinear hA.op hM) := by
  let _ := bidualAction hA.op hM
  let _ := rightBidualAction hA hM
  let _ := NondegenerateScalars.complexModule hA.op hM
  let _ := NondegenerateScalars.complexModule hA.op (bidual_isNondegenerate hA.op hM)
  let _ := NondegenerateScalars.complexModule hA.op (rightBidual_isNondegenerate hA hM)
  apply LinearMap.ext
  intro m
  rfl

@[simp] theorem rightEvaluationLinear_apply (m : M) (φ : Dual hA.op hM) :
    (rightEvaluationLinear hA hM m).val φ = φ.val m := rfl

variable {N : Type uN} [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
  (hN : IsNondegenerate Aᵐᵒᵖ N)

/-- Naturality follows by composing the two published whole-map naturality laws. -/
theorem rightEvaluation_naturality (f : NonUnitalModuleHom Aᵐᵒᵖ M N) :
    letI := rightBidualAction hA hM
    letI := rightBidualAction hA hN
    (rightDoublePullback hA hM hN f).comp (rightEvaluation hA hM) =
      (rightEvaluation hA hN).comp f := by
  let _ := bidualAction hA.op hM
  let _ := bidualAction hA.op hN
  let _ := rightBidualAction hA hM
  let _ := rightBidualAction hA hN
  calc
    (rightDoublePullback hA hM hN f).comp (rightEvaluation hA hM) =
        ((rightDoublePullback hA hM hN f).comp (comparisonHom hA hM)).comp
          (evaluation hA.op hM) := rfl
    _ = ((comparisonHom hA hN).comp (doublePullback hA.op hM hN f)).comp
          (evaluation hA.op hM) :=
      congrArg (fun g => g.comp (evaluation hA.op hM)) (comparison_naturality hA hM hN f)
    _ = (comparisonHom hA hN).comp
          ((doublePullback hA.op hM hN f).comp (evaluation hA.op hM)) := rfl
    _ = (comparisonHom hA hN).comp ((evaluation hA.op hN).comp f) :=
      congrArg (fun g => (comparisonHom hA hN).comp g)
        (evaluation_naturality hA.op hM hN f)
    _ = (rightEvaluation hA hN).comp f := rfl

theorem rightEvaluation_linear_naturality (f : NonUnitalModuleHom Aᵐᵒᵖ M N) :
    letI := rightBidualAction hA hM
    letI := rightBidualAction hA hN
    letI := NondegenerateScalars.complexModule hA.op hM
    letI := NondegenerateScalars.complexModule hA.op hN
    letI := NondegenerateScalars.complexModule hA.op (rightBidual_isNondegenerate hA hM)
    letI := NondegenerateScalars.complexModule hA.op (rightBidual_isNondegenerate hA hN)
    (NondegenerateScalars.complexToLinearMap hA.op
      (rightBidual_isNondegenerate hA hM) (rightBidual_isNondegenerate hA hN)
      (rightDoublePullback hA hM hN f)).comp (rightEvaluationLinear hA hM) =
        (rightEvaluationLinear hA hN).comp
          (NondegenerateScalars.complexToLinearMap hA.op hM hN f) := by
  let _ := rightBidualAction hA hM
  let _ := rightBidualAction hA hN
  let _ := NondegenerateScalars.complexModule hA.op hM
  let _ := NondegenerateScalars.complexModule hA.op hN
  let _ := NondegenerateScalars.complexModule hA.op (rightBidual_isNondegenerate hA hM)
  let _ := NondegenerateScalars.complexModule hA.op (rightBidual_isNondegenerate hA hN)
  apply LinearMap.ext
  intro m
  exact congrArg (fun g => g m) (rightEvaluation_naturality hA hM hN f)

end Original

section Categorical

/-- The published evaluation followed by the actual right comparison. -/
def rightEvaluationNatTrans (hA : IsIdempotented A) :
    𝟭 (RightNondegenerateModuleCat.{uA,uM} A) ⟶ actualRightBidualFunctor hA :=
  evaluationNatTrans hA.op ≫ (comparisonNatIso hA).hom

theorem rightEvaluationNatTrans_eq_transport (hA : IsIdempotented A) :
    rightEvaluationNatTrans.{uA,uM} hA =
      evaluationNatTrans hA.op ≫ (comparisonNatIso hA).hom := rfl

theorem rightEvaluationNatTrans_app_eq_transport (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA,uM} A) :
    (rightEvaluationNatTrans hA).app M =
      (evaluationNatTrans hA.op).app M ≫ (comparisonNatIso hA).hom.app M := rfl

theorem rightEvaluationNatTrans_app_hom (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA,uM} A) :
    letI := rightBidualAction hA M.property
    ((rightEvaluationNatTrans hA).app M).hom = rightEvaluation hA M.property := rfl

theorem rightEvaluationNatTrans_app_toAddMonoidHom (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA,uM} A) :
    ((rightEvaluationNatTrans hA).app M).hom.toAddMonoidHom =
      (rightEvaluation hA M.property).toAddMonoidHom := rfl

theorem rightEvaluationNatTrans_app_val (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA,uM} A) (m : M.obj) :
    letI := firstDualAction hA M.property
    (NonUnitalModuleHom.toAddMonoidHom ((rightEvaluationNatTrans hA).app M).hom m).val =
      fullComparison hA (isNondegenerate hA.op M.property)
        (fullEvaluation hA.op M.property m) := rfl

theorem rightEvaluationNatTrans_app_val_coe (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA,uM} A) (m : M.obj) :
    ⇑(NonUnitalModuleHom.toAddMonoidHom ((rightEvaluationNatTrans hA).app M).hom m).val =
      fun φ => φ.val m := rfl

@[simp] theorem rightEvaluationNatTrans_app_apply (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA,uM} A) (m : M.obj)
    (φ : (rightDualObject hA M).obj) :
    (NonUnitalModuleHom.toAddMonoidHom ((rightEvaluationNatTrans hA).app M).hom m).val φ =
      φ.val m := rfl

set_option maxHeartbeats 800000 in
theorem rightEvaluationNatTrans_naturality_hom (hA : IsIdempotented A)
    {M N : RightNondegenerateModuleCat.{uA,uM} A} (f : M ⟶ N) :
    (((actualRightBidualFunctor hA).map f).hom).comp
        ((rightEvaluationNatTrans hA).app M).hom =
      (((rightEvaluationNatTrans hA).app N).hom).comp f.hom :=
  rightEvaluation_naturality hA M.property N.property f.hom

end Categorical

end Langlands.Algebra.NonUnitalModuleRightBidual
