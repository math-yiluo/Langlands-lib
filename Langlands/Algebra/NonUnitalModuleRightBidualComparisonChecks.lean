import Langlands.Algebra.NonUnitalModuleRightBidualComparison

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleRightBidual

open CategoryTheory MulOpposite NonUnitalModuleDual

universe uA uM uN

/-! Complete unapplied original-carrier interfaces. -/

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    NonUnitalModule Aᵐᵒᵖᵐᵒᵖ (Dual hA.op hM) :=
  @rawFirstDualAction.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    NonUnitalModule A (Dual hA.op hM) :=
  @firstDualAction.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    letI := firstDualAction hA hM
    letI := fullAction hA (firstDual_isNondegenerate hA hM)
    NonUnitalSubmodule Aᵐᵒᵖ (FullDual hA (firstDual_isNondegenerate hA hM)) :=
  @RightBidual.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    NonUnitalModule Aᵐᵒᵖ (RightBidual hA hM) :=
  @rightBidualAction.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    letI := bidualAction hA.op hM
    letI := rightBidualAction hA hM
    NonUnitalModuleHom Aᵐᵒᵖ (Bidual hA.op hM) (RightBidual hA hM) :=
  @comparisonHom.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    letI := bidualAction hA.op hM
    letI := rightBidualAction hA hM
    NonUnitalModuleHom Aᵐᵒᵖ (RightBidual hA hM) (Bidual hA.op hM) :=
  @comparisonInvHom.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    letI := bidualAction hA.op hM
    letI := rightBidualAction hA hM
    letI := NondegenerateScalars.complexModule hA.op (bidual_isNondegenerate hA.op hM)
    letI := NondegenerateScalars.complexModule hA.op (rightBidual_isNondegenerate hA hM)
    Bidual hA.op hM ≃ₗ[ℂ] RightBidual hA hM :=
  @comparisonLinear.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    letI := firstDualAction hA hM
    NondegenerateScalars.complexModule hA (firstDual_isNondegenerate hA hM) =
      NondegenerateScalars.complexModule hA.op.op (isNondegenerate hA.op hM) :=
  @firstDualCanonicalModule_eq.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    {N : Type uN} → [AddCommGroup N] → [NonUnitalModule Aᵐᵒᵖ N] →
    (hN : IsNondegenerate Aᵐᵒᵖ N) →
    (f : NonUnitalModuleHom Aᵐᵒᵖ M N) →
    letI := bidualAction hA.op hM
    letI := bidualAction hA.op hN
    letI := rightBidualAction hA hM
    letI := rightBidualAction hA hN
    (rightDoublePullback hA hM hN f).comp (comparisonHom hA hM) =
      (comparisonHom hA hN).comp (doublePullback hA.op hM hN f) :=
  @comparison_naturality.{uA,uM,uN}

/-! Complete categorical interfaces target the exact right composite. -/

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    (hA : IsIdempotented A) →
    RightNondegenerateModuleCat.{uA,uM} A ⥤ RightNondegenerateModuleCat.{uA,uM} A :=
  @actualRightBidualFunctor.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    (hA : IsIdempotented A) →
    bidualFunctor.{uA,uM} hA.op ≅
      (rightToLeftFunctor hA).rightOp ⋙ leftToRightFunctor hA :=
  @comparisonNatIso.{uA,uM}

example :
    {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    (hA : IsIdempotented A) →
    {M N : RightNondegenerateModuleCat.{uA,uM} A} → (f : M ⟶ N) →
    (((actualRightBidualFunctor hA).map f).hom).comp (actualComparisonHom hA M) =
      (actualComparisonHom hA N).comp (((bidualFunctor hA.op).map f).hom) :=
  @actualComparison_naturality.{uA,uM}

/-! Strict unequal universes in both algebra/carrier directions. -/

example :
    {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    letI := firstDualAction hA hM
    letI := fullAction hA (firstDual_isNondegenerate hA hM)
    NonUnitalSubmodule Aᵐᵒᵖ (FullDual hA (firstDual_isNondegenerate hA hM)) :=
  @RightBidual.{0,1}

example :
    {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    letI := bidualAction hA.op hM
    letI := rightBidualAction hA hM
    letI := NondegenerateScalars.complexModule hA.op (bidual_isNondegenerate hA.op hM)
    letI := NondegenerateScalars.complexModule hA.op (rightBidual_isNondegenerate hA hM)
    Bidual hA.op hM ≃ₗ[ℂ] RightBidual hA hM :=
  @comparisonLinear.{0,1}

example :
    {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    (hA : IsIdempotented A) →
    bidualFunctor.{0,1} hA.op ≅
      (rightToLeftFunctor hA).rightOp ⋙ leftToRightFunctor hA :=
  @comparisonNatIso.{0,1}

example :
    {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    letI := firstDualAction hA hM
    letI := fullAction hA (firstDual_isNondegenerate hA hM)
    NonUnitalSubmodule Aᵐᵒᵖ (FullDual hA (firstDual_isNondegenerate hA hM)) :=
  @RightBidual.{1,0}

example :
    {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    letI := bidualAction hA.op hM
    letI := rightBidualAction hA hM
    letI := NondegenerateScalars.complexModule hA.op (bidual_isNondegenerate hA.op hM)
    letI := NondegenerateScalars.complexModule hA.op (rightBidual_isNondegenerate hA hM)
    Bidual hA.op hM ≃ₗ[ℂ] RightBidual hA hM :=
  @comparisonLinear.{1,0}

example :
    {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    (hA : IsIdempotented A) →
    bidualFunctor.{1,0} hA.op ≅
      (rightToLeftFunctor hA).rightOp ⋙ leftToRightFunctor hA :=
  @comparisonNatIso.{1,0}

/-! Unequal source and target carrier universes in both directions. -/

example :
    {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    {N : Type 2} → [AddCommGroup N] → [NonUnitalModule Aᵐᵒᵖ N] →
    (hN : IsNondegenerate Aᵐᵒᵖ N) →
    (f : NonUnitalModuleHom Aᵐᵒᵖ M N) →
    letI := bidualAction hA.op hM
    letI := bidualAction hA.op hN
    letI := rightBidualAction hA hM
    letI := rightBidualAction hA hN
    (rightDoublePullback hA hM hN f).comp (comparisonHom hA hM) =
      (comparisonHom hA hN).comp (doublePullback hA.op hM hN f) :=
  @comparison_naturality.{0,1,2}

example :
    {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 2} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) →
    {N : Type 0} → [AddCommGroup N] → [NonUnitalModule Aᵐᵒᵖ N] →
    (hN : IsNondegenerate Aᵐᵒᵖ N) →
    (f : NonUnitalModuleHom Aᵐᵒᵖ M N) →
    letI := bidualAction hA.op hM
    letI := bidualAction hA.op hN
    letI := rightBidualAction hA hM
    letI := rightBidualAction hA hN
    (rightDoublePullback hA hM hN f).comp (comparisonHom hA hM) =
      (comparisonHom hA hN).comp (doublePullback hA.op hM hN f) :=
  @comparison_naturality.{1,2,0}

/-! Explicit structures remain fixed when competing instances are available. -/

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
local notation "bAction₀" => @bidualAction Aᵐᵒᵖ _ _ _ _ M mGroup mAction hA.op hM
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
  [otherFirstScalars : Module ℂ
    (@Dual Aᵐᵒᵖ _ _ _ _ M mGroup mAction hA.op hM)]
  [otherGenericScalars : Module ℂ
    (@Bidual Aᵐᵒᵖ _ _ _ _ M mGroup mAction hA.op hM)]
  [otherActualScalars : Module ℂ
    (@RightBidual A aRing aScalar aTower aComm M mGroup mAction hA hM)]

include otherOriginal otherRaw otherLeft otherGeneric otherActual
  otherFirstScalars otherGenericScalars otherActualScalars

example : (inferInstance : NonUnitalModule Aᵐᵒᵖ M) = otherOriginal := rfl
example : (inferInstance : NonUnitalModule Aᵐᵒᵖᵐᵒᵖ D₀) = otherRaw := rfl
example : (inferInstance : NonUnitalModule A D₀) = otherLeft := rfl
example : (inferInstance : NonUnitalModule Aᵐᵒᵖ B₀) = otherGeneric := rfl
example : (inferInstance : NonUnitalModule Aᵐᵒᵖ R₀) = otherActual := rfl
example : (inferInstance : Module ℂ D₀) = otherFirstScalars := rfl
example : (inferInstance : Module ℂ B₀) = otherGenericScalars := rfl
example : (inferInstance : Module ℂ R₀) = otherActualScalars := rfl

example : @NonUnitalModuleHom Aᵐᵒᵖ B₀ R₀ _ _ _ bAction₀ rAction₀ :=
  @comparisonHom A aRing aScalar aTower aComm M mGroup mAction hA hM

example : @NonUnitalModuleHom Aᵐᵒᵖ R₀ B₀ _ _ _ rAction₀ bAction₀ :=
  @comparisonInvHom A aRing aScalar aTower aComm M mGroup mAction hA hM

example :
    letI := mAction
    letI := bAction₀
    letI := rAction₀
    letI := NondegenerateScalars.complexModule hA.op (bidual_isNondegenerate hA.op hM)
    letI := NondegenerateScalars.complexModule hA.op (rightBidual_isNondegenerate hA hM)
    B₀ ≃ₗ[ℂ] R₀ :=
  @comparisonLinear A aRing aScalar aTower aComm M mGroup mAction hA hM

example :
    letI := mAction
    letI := @rawFirstDualAction A aRing aScalar aTower aComm M mGroup mAction hA hM
    letI := @firstDualAction A aRing aScalar aTower aComm M mGroup mAction hA hM
    NondegenerateScalars.complexModule hA (firstDual_isNondegenerate hA hM) =
      NondegenerateScalars.complexModule hA.op.op (isNondegenerate hA.op hM) :=
  @firstDualCanonicalModule_eq A aRing aScalar aTower aComm M mGroup mAction hA hM

end CompetingStructures

end Langlands.Algebra.NonUnitalModuleRightBidual
