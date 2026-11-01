import Langlands.Algebra.NonUnitalModuleBidualEvaluation
import Mathlib.Algebra.Module.PUnit

/-!
# Complete interfaces for canonical actual bidual evaluation

These are author compilation checks for the source construction and its internal
packaging. They introduce no injectivity, exactness or right-composite comparison.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDual

open MulOpposite CategoryTheory

universe uA uM uN

/-! The complete generic interfaces, with independent universes. -/

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := fullAction hA hM
    letI := fullAction hA.op (isNondegenerate hA hM)
    NonUnitalSubmodule Aᵐᵒᵖᵐᵒᵖ (FullDual hA.op (isNondegenerate hA hM)) :=
  @Bidual.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    NonUnitalModule A (Bidual hA hM) :=
  @bidualAction.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := fullAction hA hM
    M → FullDual hA.op (isNondegenerate hA hM) :=
  @fullEvaluation.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := fullAction hA hM
    letI := NondegenerateScalars.complexModule hA hM
    M →ₗ[ℂ] FullDual hA.op (isNondegenerate hA hM) :=
  @fullEvaluationLinear.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := fullAction hA hM
    letI := fullAction hA.op (isNondegenerate hA hM)
    (m : M) → (e : Idempotent A) → (e : A) • m = m →
    op (op (e : A)) • fullEvaluation hA hM m = fullEvaluation hA hM m :=
  @fullEvaluation_fixed.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := fullAction hA hM
    letI := fullAction hA.op (isNondegenerate hA hM)
    (m : M) → fullEvaluation hA hM m ∈
      nondegeneratePart hA.op.op (FullDual hA.op (isNondegenerate hA hM)) :=
  @fullEvaluation_mem.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := bidualAction hA hM
    IsNondegenerate A (Bidual hA hM) :=
  @bidual_isNondegenerate.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := bidualAction hA hM
    NonUnitalModuleHom A M (Bidual hA hM) :=
  @evaluation.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := bidualAction hA hM
    letI := NondegenerateScalars.complexModule hA hM
    letI := NondegenerateScalars.complexModule hA (bidual_isNondegenerate hA hM)
    M →ₗ[ℂ] Bidual hA hM :=
  @evaluationLinear.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    (hA : IsIdempotented A) →
    NondegenerateModuleCat.{uA, uM} A ⥤ NondegenerateModuleCat.{uA, uM} A :=
  @bidualFunctor.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    (hA : IsIdempotented A) →
    𝟭 (NondegenerateModuleCat.{uA, uM} A) ⟶
      (leftToRightFunctor hA).rightOp ⋙ rightToLeftFunctor hA :=
  @evaluationNatTrans.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    (hA : IsIdempotented A) →
    (M : NondegenerateModuleCat.{uA, uM} A) →
    letI := bidualAction hA M.property
    ((evaluationNatTrans hA).app M).hom = evaluation hA M.property :=
  @evaluationNatTrans_app_hom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    {N : Type uN} → [AddCommGroup N] → [NonUnitalModule A N] →
    (hN : IsNondegenerate A N) →
    NonUnitalModuleHom A M N →
    letI := bidualAction hA hM
    letI := bidualAction hA hN
    NonUnitalModuleHom A (Bidual hA hM) (Bidual hA hN) :=
  @doublePullback.{uA, uM, uN}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    {N : Type uN} → [AddCommGroup N] → [NonUnitalModule A N] →
    (hN : IsNondegenerate A N) →
    (f : NonUnitalModuleHom A M N) →
    letI := bidualAction hA hM
    letI := bidualAction hA hN
    (doublePullback hA hM hN f).comp (evaluation hA hM) =
      (evaluation hA hN).comp f :=
  @evaluation_naturality.{uA, uM, uN}

/-! Both unequal algebra/carrier universe directions, without lifts. -/

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := fullAction hA hM
    letI := fullAction hA.op (isNondegenerate hA hM)
    NonUnitalSubmodule Aᵐᵒᵖᵐᵒᵖ (FullDual hA.op (isNondegenerate hA hM)) :=
  @Bidual.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    NonUnitalModule A (Bidual hA hM) :=
  @bidualAction.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := fullAction hA hM
    M → FullDual hA.op (isNondegenerate hA hM) :=
  @fullEvaluation.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := fullAction hA hM
    letI := NondegenerateScalars.complexModule hA hM
    M →ₗ[ℂ] FullDual hA.op (isNondegenerate hA hM) :=
  @fullEvaluationLinear.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := bidualAction hA hM
    IsNondegenerate A (Bidual hA hM) :=
  @bidual_isNondegenerate.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := bidualAction hA hM
    NonUnitalModuleHom A M (Bidual hA hM) :=
  @evaluation.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := bidualAction hA hM
    letI := NondegenerateScalars.complexModule hA hM
    letI := NondegenerateScalars.complexModule hA (bidual_isNondegenerate hA hM)
    M →ₗ[ℂ] Bidual hA hM :=
  @evaluationLinear.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    (hA : IsIdempotented A) →
    NondegenerateModuleCat.{0, 1} A ⥤ NondegenerateModuleCat.{0, 1} A :=
  @bidualFunctor.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    (hA : IsIdempotented A) →
    𝟭 (NondegenerateModuleCat.{0, 1} A) ⟶
      (leftToRightFunctor hA).rightOp ⋙ rightToLeftFunctor hA :=
  @evaluationNatTrans.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    (hA : IsIdempotented A) →
    (M : NondegenerateModuleCat.{0, 1} A) →
    letI := bidualAction hA M.property
    ((evaluationNatTrans hA).app M).hom = evaluation hA M.property :=
  @evaluationNatTrans_app_hom.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := fullAction hA hM
    letI := fullAction hA.op (isNondegenerate hA hM)
    NonUnitalSubmodule Aᵐᵒᵖᵐᵒᵖ (FullDual hA.op (isNondegenerate hA hM)) :=
  @Bidual.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    NonUnitalModule A (Bidual hA hM) :=
  @bidualAction.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := fullAction hA hM
    M → FullDual hA.op (isNondegenerate hA hM) :=
  @fullEvaluation.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := fullAction hA hM
    letI := NondegenerateScalars.complexModule hA hM
    M →ₗ[ℂ] FullDual hA.op (isNondegenerate hA hM) :=
  @fullEvaluationLinear.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := bidualAction hA hM
    IsNondegenerate A (Bidual hA hM) :=
  @bidual_isNondegenerate.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := bidualAction hA hM
    NonUnitalModuleHom A M (Bidual hA hM) :=
  @evaluation.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    letI := bidualAction hA hM
    letI := NondegenerateScalars.complexModule hA hM
    letI := NondegenerateScalars.complexModule hA (bidual_isNondegenerate hA hM)
    M →ₗ[ℂ] Bidual hA hM :=
  @evaluationLinear.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    (hA : IsIdempotented A) →
    NondegenerateModuleCat.{1, 0} A ⥤ NondegenerateModuleCat.{1, 0} A :=
  @bidualFunctor.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    (hA : IsIdempotented A) →
    𝟭 (NondegenerateModuleCat.{1, 0} A) ⟶
      (leftToRightFunctor hA).rightOp ⋙ rightToLeftFunctor hA :=
  @evaluationNatTrans.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    (hA : IsIdempotented A) →
    (M : NondegenerateModuleCat.{1, 0} A) →
    letI := bidualAction hA M.property
    ((evaluationNatTrans hA).app M).hom = evaluation hA M.property :=
  @evaluationNatTrans_app_hom.{1, 0}

/-! Unequal original source and target universes in both directions. -/

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    {N : Type 1} → [AddCommGroup N] → [NonUnitalModule A N] →
    (hN : IsNondegenerate A N) →
    NonUnitalModuleHom A M N →
    letI := bidualAction hA hM
    letI := bidualAction hA hN
    NonUnitalModuleHom A (Bidual hA hM) (Bidual hA hN) :=
  @doublePullback.{uA, 0, 1}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    {N : Type 1} → [AddCommGroup N] → [NonUnitalModule A N] →
    (hN : IsNondegenerate A N) →
    (f : NonUnitalModuleHom A M N) →
    letI := bidualAction hA hM
    letI := bidualAction hA hN
    (doublePullback hA hM hN f).comp (evaluation hA hM) =
      (evaluation hA hN).comp f :=
  @evaluation_naturality.{uA, 0, 1}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    {N : Type 0} → [AddCommGroup N] → [NonUnitalModule A N] →
    (hN : IsNondegenerate A N) →
    NonUnitalModuleHom A M N →
    letI := bidualAction hA hM
    letI := bidualAction hA hN
    NonUnitalModuleHom A (Bidual hA hM) (Bidual hA hN) :=
  @doublePullback.{uA, 1, 0}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    {N : Type 0} → [AddCommGroup N] → [NonUnitalModule A N] →
    (hN : IsNondegenerate A N) →
    (f : NonUnitalModuleHom A M N) →
    letI := bidualAction hA hM
    letI := bidualAction hA hN
    (doublePullback hA hM hN f).comp (evaluation hA hM) =
      (evaluation hA hN).comp f :=
  @evaluation_naturality.{uA, 1, 0}

/-! Competing actions and scalar modules do not replace the specified structures. -/

section CompetingStructures

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

variable {A : Type uA} [aRing : NonUnitalRing A] [aScalar : Module ℂ A]
  [aTower : IsScalarTower ℂ A A] [aComm : SMulCommClass ℂ A A]
  {M : Type uM} [mGroup : AddCommGroup M] [mAction : NonUnitalModule A M]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M)

local notation "D₀" => @Dual A aRing aScalar aTower aComm M mGroup mAction hA hM
local notation "B₀" => @Bidual A aRing aScalar aTower aComm M mGroup mAction hA hM
local notation "bAction₀" =>
  @bidualAction A aRing aScalar aTower aComm M mGroup mAction hA hM

variable [otherOriginal : NonUnitalModule A M]
  [otherDual : NonUnitalModule Aᵐᵒᵖ
    (@Dual A aRing aScalar aTower aComm M mGroup mAction hA hM)]
  [otherBidual : NonUnitalModule A
    (@Bidual A aRing aScalar aTower aComm M mGroup mAction hA hM)]
  [otherSourceScalars : Module ℂ M]
  [otherDualScalars : Module ℂ
    (@Dual A aRing aScalar aTower aComm M mGroup mAction hA hM)]
  [otherBidualScalars : Module ℂ
    (@Bidual A aRing aScalar aTower aComm M mGroup mAction hA hM)]

include otherOriginal otherDual otherBidual
  otherSourceScalars otherDualScalars otherBidualScalars

example : (inferInstance : NonUnitalModule A M) = otherOriginal := rfl
example : (inferInstance : NonUnitalModule Aᵐᵒᵖ D₀) = otherDual := rfl
example : (inferInstance : NonUnitalModule A B₀) = otherBidual := rfl
example : (inferInstance : Module ℂ M) = otherSourceScalars := rfl
example : (inferInstance : Module ℂ D₀) = otherDualScalars := rfl
example : (inferInstance : Module ℂ B₀) = otherBidualScalars := rfl

example : @NonUnitalModuleHom A M B₀ aRing mGroup _ mAction bAction₀ :=
  @evaluation A aRing aScalar aTower aComm M mGroup mAction hA hM

example :
    letI := mAction
    letI := fullAction hA hM
    letI := dualAction hA hM
    M → FullDual hA.op (isNondegenerate hA hM) :=
  @fullEvaluation A aRing aScalar aTower aComm M mGroup mAction hA hM

example :
    letI := mAction
    letI := fullAction hA hM
    letI := dualAction hA hM
    letI := NondegenerateScalars.complexModule hA hM
    M →ₗ[ℂ] FullDual hA.op (isNondegenerate hA hM) :=
  @fullEvaluationLinear A aRing aScalar aTower aComm M mGroup mAction hA hM

example :
    letI := mAction
    letI := bAction₀
    letI := NondegenerateScalars.complexModule hA hM
    letI := NondegenerateScalars.complexModule hA (bidual_isNondegenerate hA hM)
    M →ₗ[ℂ] B₀ :=
  @evaluationLinear A aRing aScalar aTower aComm M mGroup mAction hA hM

example (a : A) (m : M) :
    (@evaluation A aRing aScalar aTower aComm M mGroup mAction hA hM)
        (mAction.toDistribSMul.toSMul.smul a m) =
      (bAction₀).toDistribSMul.toSMul.smul a
        ((@evaluation A aRing aScalar aTower aComm M mGroup mAction hA hM) m) :=
  @evaluation_map_smul A aRing aScalar aTower aComm M mGroup mAction hA hM a m

example (a : A) (Φ : B₀) (φ : D₀) :
    ((bAction₀).toDistribSMul.toSMul.smul a Φ).val φ =
      Φ.val ((@dualAction A aRing aScalar aTower aComm M mGroup mAction hA hM).toDistribSMul.toSMul.smul
        (op a) φ) :=
  @bidualAction_smul_apply A aRing aScalar aTower aComm M mGroup mAction hA hM a Φ φ

example (c : ℂ) (φ : D₀) (m : M) :
    letI := mAction
    letI := fullAction hA hM
    letI := dualAction hA hM
    letI := NondegenerateScalars.complexModule hA.op (isNondegenerate hA hM)
    (c • φ).val m = c • φ.val m := by
  let _ := mAction
  let _ := fullAction hA hM
  let _ := dualAction hA hM
  exact canonical_smul_apply hA hM c φ m

example (c : ℂ) (m : M) :
    letI := mAction
    letI := bAction₀
    letI := NondegenerateScalars.complexModule hA hM
    letI := NondegenerateScalars.complexModule hA (bidual_isNondegenerate hA hM)
    evaluationLinear hA hM (c • m) = c • evaluationLinear hA hM m := by
  let _ := mAction
  let _ := bAction₀
  let _ := NondegenerateScalars.complexModule hA hM
  let _ := NondegenerateScalars.complexModule hA (bidual_isNondegenerate hA hM)
  exact (evaluationLinear hA hM).map_smul c m

end CompetingStructures

/-! Generic specialization to original right modules, without a right-composite claim. -/

section RightModules

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]

example : {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented Aᵐᵒᵖ) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    letI := bidualAction hA hM
    NonUnitalModuleHom Aᵐᵒᵖ M (Bidual hA hM) :=
  @evaluation.{uA, uM} Aᵐᵒᵖ _ _ _ _

example {M : Type uM} [AddCommGroup M] [NonUnitalModule Aᵐᵒᵖ M]
    (hA : IsIdempotented A) (hM : IsNondegenerate Aᵐᵒᵖ M) :
    letI := bidualAction hA.op hM
    NonUnitalModuleHom Aᵐᵒᵖ M (Bidual hA.op hM) :=
  evaluation hA.op hM

example {M : Type uM} [AddCommGroup M] [NonUnitalModule Aᵐᵒᵖ M]
    {N : Type uN} [AddCommGroup N] [NonUnitalModule Aᵐᵒᵖ N]
    (hA : IsIdempotented A) (hM : IsNondegenerate Aᵐᵒᵖ M)
    (hN : IsNondegenerate Aᵐᵒᵖ N) (f : NonUnitalModuleHom Aᵐᵒᵖ M N) :
    letI := bidualAction hA.op hM
    letI := bidualAction hA.op hN
    (doublePullback hA.op hM hN f).comp (evaluation hA.op hM) =
      (evaluation hA.op hN).comp f :=
  evaluation_naturality hA.op hM hN f

end RightModules

/-! Zero module and algebra carriers at independent universes. -/

section ZeroCarriers

private theorem punit_isNondegenerate (A : Type uA) [NonUnitalRing A]
    [NonUnitalModule A PUnit.{uM + 1}] : IsNondegenerate A PUnit.{uM + 1} := by
  intro m
  exact ⟨⟨0, IsIdempotentElem.zero⟩, Subsingleton.elim _ _⟩

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A)

local instance : NonUnitalModule A PUnit.{uM + 1} := NonUnitalModule.zero

example :
    letI := bidualAction hA (punit_isNondegenerate.{uA, uM} A)
    NonUnitalModuleHom A PUnit.{uM + 1} (Bidual hA (punit_isNondegenerate A)) :=
  evaluation hA (punit_isNondegenerate A)

example (φ : Dual hA (punit_isNondegenerate.{uA, uM} A)) :
    (evaluation hA (punit_isNondegenerate A) PUnit.unit).val φ = 0 := by
  change φ.val (0 : PUnit) = 0
  exact φ.val.map_zero

example :
    letI := bidualAction hA (punit_isNondegenerate.{uA, uM} A)
    letI := NondegenerateScalars.complexModule hA (punit_isNondegenerate A)
    letI := NondegenerateScalars.complexModule hA
      (bidual_isNondegenerate hA (punit_isNondegenerate A))
    PUnit.{uM + 1} →ₗ[ℂ] Bidual hA (punit_isNondegenerate A) :=
  evaluationLinear hA (punit_isNondegenerate A)

example :
    𝟭 (NondegenerateModuleCat.{uA, uM} PUnit.{uA + 1}) ⟶
      (leftToRightFunctor (IsIdempotented.of_ring PUnit)).rightOp ⋙
        rightToLeftFunctor (IsIdempotented.of_ring PUnit) :=
  evaluationNatTrans (IsIdempotented.of_ring PUnit)

example :
    let h₀ := IsIdempotented.of_ring PUnit.{uA + 1}
    letI : NonUnitalModule PUnit.{uA + 1} PUnit.{uM + 1} := NonUnitalModule.zero
    letI := bidualAction h₀ (punit_isNondegenerate PUnit)
    NonUnitalModuleHom PUnit.{uA + 1} PUnit.{uM + 1}
      (Bidual h₀ (punit_isNondegenerate PUnit)) := by
  letI : NonUnitalModule PUnit.{uA + 1} PUnit.{uM + 1} := NonUnitalModule.zero
  exact evaluation (IsIdempotented.of_ring PUnit) (punit_isNondegenerate PUnit)

end ZeroCarriers

end Langlands.Algebra.NonUnitalModuleDual
