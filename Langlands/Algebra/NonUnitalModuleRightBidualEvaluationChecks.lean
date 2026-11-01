import Langlands.Algebra.NonUnitalModuleRightBidualEvaluation

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleRightBidual

open CategoryTheory MulOpposite NonUnitalModuleDual

universe uA uM uN

/-! Complete unapplied original-carrier evaluation interfaces. -/

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    letI := rightBidualAction hA hM
    NonUnitalModuleHom Aᵐᵒᵖ M (RightBidual hA hM) :=
  @rightEvaluation.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    letI := rightBidualAction hA hM
    letI := NondegenerateScalars.complexModule hA.op hM
    letI := NondegenerateScalars.complexModule hA.op (rightBidual_isNondegenerate hA hM)
    M →ₗ[ℂ] RightBidual hA hM :=
  @rightEvaluationLinear.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    letI := bidualAction hA.op hM
    letI := rightBidualAction hA hM
    rightEvaluation hA hM = (comparisonHom hA hM).comp (evaluation hA.op hM) :=
  @rightEvaluation_eq_transport.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    (m : M) → ⇑(rightEvaluation hA hM m).val = fun φ => φ.val m :=
  @rightEvaluation_val_coe.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    letI := bidualAction hA.op hM
    letI := rightBidualAction hA hM
    letI := NondegenerateScalars.complexModule hA.op hM
    letI := NondegenerateScalars.complexModule hA.op (bidual_isNondegenerate hA.op hM)
    letI := NondegenerateScalars.complexModule hA.op (rightBidual_isNondegenerate hA hM)
    rightEvaluationLinear hA hM =
      (comparisonLinear hA hM).toLinearMap.comp (evaluationLinear hA.op hM) :=
  @rightEvaluationLinear_eq_transport.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    {N : Type uN} → [AddCommGroup N] → [NonUnitalModule Aᵐᵒᵖ N] →
    (hN : IsNondegenerate Aᵐᵒᵖ N) →
    (f : NonUnitalModuleHom Aᵐᵒᵖ M N) →
    letI := rightBidualAction hA hM
    letI := rightBidualAction hA hN
    (rightDoublePullback hA hM hN f).comp (rightEvaluation hA hM) =
      (rightEvaluation hA hN).comp f :=
  @rightEvaluation_naturality.{uA,uM,uN}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    {N : Type uN} → [AddCommGroup N] → [NonUnitalModule Aᵐᵒᵖ N] →
    (hN : IsNondegenerate Aᵐᵒᵖ N) →
    (f : NonUnitalModuleHom Aᵐᵒᵖ M N) →
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
          (NondegenerateScalars.complexToLinearMap hA.op hM hN f) :=
  @rightEvaluation_linear_naturality.{uA,uM,uN}

/-! Complete interfaces for the exact right categorical composite. -/

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    (hA : IsIdempotented A) →
    𝟭 (RightNondegenerateModuleCat.{uA,uM} A) ⟶
      (rightToLeftFunctor hA).rightOp ⋙ leftToRightFunctor hA :=
  @rightEvaluationNatTrans.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    (hA : IsIdempotented A) →
    (M : RightNondegenerateModuleCat.{uA,uM} A) →
    letI := rightBidualAction hA M.property
    ((rightEvaluationNatTrans hA).app M).hom = rightEvaluation hA M.property :=
  @rightEvaluationNatTrans_app_hom.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    (hA : IsIdempotented A) →
    {M N : RightNondegenerateModuleCat.{uA,uM} A} → (f : M ⟶ N) →
    (((actualRightBidualFunctor hA).map f).hom).comp
        ((rightEvaluationNatTrans hA).app M).hom =
      (((rightEvaluationNatTrans hA).app N).hom).comp f.hom :=
  @rightEvaluationNatTrans_naturality_hom.{uA,uM}

/-! Both strict unequal algebra/carrier universe directions. -/

example :
    {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    letI := rightBidualAction hA hM
    NonUnitalModuleHom Aᵐᵒᵖ M (RightBidual hA hM) :=
  @rightEvaluation.{0,1}

example :
    {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    letI := rightBidualAction hA hM
    letI := NondegenerateScalars.complexModule hA.op hM
    letI := NondegenerateScalars.complexModule hA.op (rightBidual_isNondegenerate hA hM)
    M →ₗ[ℂ] RightBidual hA hM :=
  @rightEvaluationLinear.{0,1}

example :
    {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    (hA : IsIdempotented A) →
    𝟭 (RightNondegenerateModuleCat.{0,1} A) ⟶
      (rightToLeftFunctor hA).rightOp ⋙ leftToRightFunctor hA :=
  @rightEvaluationNatTrans.{0,1}

example :
    {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    letI := rightBidualAction hA hM
    NonUnitalModuleHom Aᵐᵒᵖ M (RightBidual hA hM) :=
  @rightEvaluation.{1,0}

example :
    {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    letI := rightBidualAction hA hM
    letI := NondegenerateScalars.complexModule hA.op hM
    letI := NondegenerateScalars.complexModule hA.op (rightBidual_isNondegenerate hA hM)
    M →ₗ[ℂ] RightBidual hA hM :=
  @rightEvaluationLinear.{1,0}

example :
    {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    (hA : IsIdempotented A) →
    𝟭 (RightNondegenerateModuleCat.{1,0} A) ⟶
      (rightToLeftFunctor hA).rightOp ⋙ leftToRightFunctor hA :=
  @rightEvaluationNatTrans.{1,0}

/-! Original-map and linear naturality at unequal source/target universes. -/

example :
    {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    {N : Type 2} → [AddCommGroup N] → [NonUnitalModule Aᵐᵒᵖ N] →
    (hN : IsNondegenerate Aᵐᵒᵖ N) →
    (f : NonUnitalModuleHom Aᵐᵒᵖ M N) →
    letI := rightBidualAction hA hM
    letI := rightBidualAction hA hN
    (rightDoublePullback hA hM hN f).comp (rightEvaluation hA hM) =
      (rightEvaluation hA hN).comp f :=
  @rightEvaluation_naturality.{0,1,2}

example :
    {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    {N : Type 2} → [AddCommGroup N] → [NonUnitalModule Aᵐᵒᵖ N] →
    (hN : IsNondegenerate Aᵐᵒᵖ N) →
    (f : NonUnitalModuleHom Aᵐᵒᵖ M N) →
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
          (NondegenerateScalars.complexToLinearMap hA.op hM hN f) :=
  @rightEvaluation_linear_naturality.{0,1,2}

example :
    {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 2} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    {N : Type 0} → [AddCommGroup N] → [NonUnitalModule Aᵐᵒᵖ N] →
    (hN : IsNondegenerate Aᵐᵒᵖ N) →
    (f : NonUnitalModuleHom Aᵐᵒᵖ M N) →
    letI := rightBidualAction hA hM
    letI := rightBidualAction hA hN
    (rightDoublePullback hA hM hN f).comp (rightEvaluation hA hM) =
      (rightEvaluation hA hN).comp f :=
  @rightEvaluation_naturality.{1,2,0}

example :
    {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 2} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    {N : Type 0} → [AddCommGroup N] → [NonUnitalModule Aᵐᵒᵖ N] →
    (hN : IsNondegenerate Aᵐᵒᵖ N) →
    (f : NonUnitalModuleHom Aᵐᵒᵖ M N) →
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
          (NondegenerateScalars.complexToLinearMap hA.op hM hN f) :=
  @rightEvaluation_linear_naturality.{1,2,0}

/-! Pin every intended action and scalar structure despite alternatives. -/

section CompetingStructures

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

variable {A : Type uA} [aRing : NonUnitalRing A] [aScalar : Module ℂ A]
  [aTower : IsScalarTower ℂ A A] [aComm : SMulCommClass ℂ A A]
  {M : Type uM} [mGroup : AddCommGroup M] [mAction : NonUnitalModule Aᵐᵒᵖ M]
  (hA : IsIdempotented A) (hM : IsNondegenerate Aᵐᵒᵖ M)

local notation "D₀" => @Dual Aᵐᵒᵖ _ _ _ _ M mGroup mAction hA.op hM
local notation "B₀" => @Bidual Aᵐᵒᵖ _ _ _ _ M mGroup mAction hA.op hM
local notation "R₀" => @RightBidual A aRing aScalar aTower aComm M mGroup mAction hA hM
local notation "rAction₀" =>
  @rightBidualAction A aRing aScalar aTower aComm M mGroup mAction hA hM

variable [otherOriginal : NonUnitalModule Aᵐᵒᵖ M]
  [otherRaw : NonUnitalModule Aᵐᵒᵖᵐᵒᵖ
    (@Dual Aᵐᵒᵖ _ _ _ _ M mGroup mAction hA.op hM)]
  [otherLeft : NonUnitalModule A
    (@Dual Aᵐᵒᵖ _ _ _ _ M mGroup mAction hA.op hM)]
  [otherGeneric : NonUnitalModule Aᵐᵒᵖ
    (@Bidual Aᵐᵒᵖ _ _ _ _ M mGroup mAction hA.op hM)]
  [otherActual : NonUnitalModule Aᵐᵒᵖ
    (@RightBidual A aRing aScalar aTower aComm M mGroup mAction hA hM)]
  [otherSourceScalars : Module ℂ M]
  [otherFirstScalars : Module ℂ
    (@Dual Aᵐᵒᵖ _ _ _ _ M mGroup mAction hA.op hM)]
  [otherGenericScalars : Module ℂ
    (@Bidual Aᵐᵒᵖ _ _ _ _ M mGroup mAction hA.op hM)]
  [otherActualScalars : Module ℂ
    (@RightBidual A aRing aScalar aTower aComm M mGroup mAction hA hM)]

include otherOriginal otherRaw otherLeft otherGeneric otherActual
  otherSourceScalars otherFirstScalars otherGenericScalars otherActualScalars

example : (inferInstance : NonUnitalModule Aᵐᵒᵖ M) = otherOriginal := rfl
example : (inferInstance : NonUnitalModule Aᵐᵒᵖᵐᵒᵖ D₀) = otherRaw := rfl
example : (inferInstance : NonUnitalModule A D₀) = otherLeft := rfl
example : (inferInstance : NonUnitalModule Aᵐᵒᵖ B₀) = otherGeneric := rfl
example : (inferInstance : NonUnitalModule Aᵐᵒᵖ R₀) = otherActual := rfl
example : (inferInstance : Module ℂ M) = otherSourceScalars := rfl
example : (inferInstance : Module ℂ D₀) = otherFirstScalars := rfl
example : (inferInstance : Module ℂ B₀) = otherGenericScalars := rfl
example : (inferInstance : Module ℂ R₀) = otherActualScalars := rfl

example : @NonUnitalModuleHom Aᵐᵒᵖ M R₀ _ mGroup _ mAction rAction₀ :=
  @rightEvaluation A aRing aScalar aTower aComm M mGroup mAction hA hM

example :
    letI := mAction
    letI := rAction₀
    letI := NondegenerateScalars.complexModule hA.op hM
    letI := NondegenerateScalars.complexModule hA.op (rightBidual_isNondegenerate hA hM)
    M →ₗ[ℂ] R₀ :=
  @rightEvaluationLinear A aRing aScalar aTower aComm M mGroup mAction hA hM

example (a : Aᵐᵒᵖ) (m : M) :
    (@rightEvaluation A aRing aScalar aTower aComm M mGroup mAction hA hM)
        (mAction.toDistribSMul.toSMul.smul a m) =
      (rAction₀).toDistribSMul.toSMul.smul a
        ((@rightEvaluation A aRing aScalar aTower aComm M mGroup mAction hA hM) m) :=
  @rightEvaluation_map_smul A aRing aScalar aTower aComm M mGroup mAction hA hM a m

end CompetingStructures

/-! Zero algebra and module carriers at independent universes. -/

section ZeroCarriers

private theorem rightPUnit_isNondegenerate (A : Type uA) [NonUnitalRing A]
    [NonUnitalModule A PUnit.{uM + 1}] : IsNondegenerate A PUnit.{uM + 1} := by
  intro m
  exact ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A)

local instance : NonUnitalModule Aᵐᵒᵖ PUnit.{uM + 1} := NonUnitalModule.zero

example :
    letI := rightBidualAction hA (rightPUnit_isNondegenerate.{uA,uM} Aᵐᵒᵖ)
    NonUnitalModuleHom Aᵐᵒᵖ PUnit.{uM + 1}
      (RightBidual hA (rightPUnit_isNondegenerate Aᵐᵒᵖ)) :=
  rightEvaluation hA (rightPUnit_isNondegenerate Aᵐᵒᵖ)

example (φ : Dual hA.op (rightPUnit_isNondegenerate.{uA,uM} Aᵐᵒᵖ)) :
    (rightEvaluation hA (rightPUnit_isNondegenerate Aᵐᵒᵖ) PUnit.unit).val φ = 0 := by
  change φ.val (0 : PUnit) = 0
  exact φ.val.map_zero

example :
    𝟭 (RightNondegenerateModuleCat.{uA,uM} PUnit.{uA + 1}) ⟶
      (rightToLeftFunctor (IsIdempotented.of_ring PUnit)).rightOp ⋙
        leftToRightFunctor (IsIdempotented.of_ring PUnit) :=
  rightEvaluationNatTrans (IsIdempotented.of_ring PUnit)

end ZeroCarriers

end Langlands.Algebra.NonUnitalModuleRightBidual
