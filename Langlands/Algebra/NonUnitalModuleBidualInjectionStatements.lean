import Langlands.Algebra.NonUnitalModuleBidualEvaluation
import Langlands.Algebra.NonUnitalModuleRightBidualEvaluation

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleBidualInjectionStatements

open CategoryTheory NonUnitalModuleDual NonUnitalModuleRightBidual

universe uA uM

section Left

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M)

/-- The actual nondegenerate dual detects every nonzero original vector. -/
def LeftSeparation : Prop :=
  ∀ m : M, m ≠ 0 → ∃ φ : Dual hA hM, φ.val m ≠ 0

/-- Injectivity of the exact original evaluation and its recovered linear map. -/
def LeftEvaluationInjective : Prop :=
  letI := bidualAction hA hM
  letI := NondegenerateScalars.complexModule hA hM
  letI := NondegenerateScalars.complexModule hA (bidual_isNondegenerate hA hM)
  Function.Injective (evaluation hA hM) ∧
    Function.Injective (evaluationLinear hA hM)

end Left

section Right

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule Aᵐᵒᵖ M]
  (hA : IsIdempotented A) (hM : IsNondegenerate Aᵐᵒᵖ M)

/-- Separation on the original right module uses its actual first dual. -/
def RightSeparation : Prop :=
  ∀ m : M, m ≠ 0 → ∃ φ : Dual hA.op hM, φ.val m ≠ 0

/-- Both maps land in the actual right bidual after first-dual transport. -/
def RightEvaluationInjective : Prop :=
  letI := rightBidualAction hA hM
  letI := NondegenerateScalars.complexModule hA.op hM
  letI := NondegenerateScalars.complexModule hA.op (rightBidual_isNondegenerate hA hM)
  Function.Injective (rightEvaluation hA hM) ∧
    Function.Injective (rightEvaluationLinear hA hM)

end Right

section Categorical

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]

/-- Monomorphy of the exact published evaluation components in both categories. -/
def EvaluationMonomorphisms (hA : IsIdempotented A) : Prop :=
  (∀ M : NondegenerateModuleCat.{uA, uM} A,
    Mono ((evaluationNatTrans hA).app M)) ∧
  (∀ M : RightNondegenerateModuleCat.{uA, uM} A,
    Mono ((rightEvaluationNatTrans hA).app M))

end Categorical

/-- Renard I.4.1 canonical injection, with separation and both actual orientations. -/
def BidualInjection : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A),
    (∀ (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
      (hM : IsNondegenerate A M),
      LeftSeparation hA hM ∧ LeftEvaluationInjective hA hM) ∧
    (∀ (M : Type uM) [AddCommGroup M] [NonUnitalModule Aᵐᵒᵖ M]
      (hM : IsNondegenerate Aᵐᵒᵖ M),
      RightSeparation hA hM ∧ RightEvaluationInjective hA hM) ∧
    EvaluationMonomorphisms.{uA, uM} hA

/-! Complete unapplied interfaces and the closed body are checked below. -/

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) → Prop :=
  @LeftSeparation.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) → Prop :=
  @LeftEvaluationInjective.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) → Prop :=
  @RightSeparation.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) → Prop :=
  @RightEvaluationInjective.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    (hA : IsIdempotented A) → Prop := @EvaluationMonomorphisms.{uA, uM}

example : Prop := BidualInjection.{uA, uM}

example : BidualInjection.{uA, uM} =
    (∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
      [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A),
      (∀ (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
        (hM : IsNondegenerate A M),
        LeftSeparation hA hM ∧ LeftEvaluationInjective hA hM) ∧
      (∀ (M : Type uM) [AddCommGroup M] [NonUnitalModule Aᵐᵒᵖ M]
        (hM : IsNondegenerate Aᵐᵒᵖ M),
        RightSeparation hA hM ∧ RightEvaluationInjective hA hM) ∧
      EvaluationMonomorphisms.{uA, uM} hA) := rfl

/-! Unequal universes: algebra in Type 0, module in Type 1. -/

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) → Prop :=
  @LeftSeparation.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) → Prop :=
  @LeftEvaluationInjective.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) → Prop :=
  @RightSeparation.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) → Prop :=
  @RightEvaluationInjective.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    (hA : IsIdempotented A) → Prop := @EvaluationMonomorphisms.{0, 1}

example : Prop := BidualInjection.{0, 1}

example : BidualInjection.{0, 1} =
    (∀ (A : Type 0) [NonUnitalRing A] [Module ℂ A]
      [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A),
      (∀ (M : Type 1) [AddCommGroup M] [NonUnitalModule A M]
        (hM : IsNondegenerate A M),
        LeftSeparation hA hM ∧ LeftEvaluationInjective hA hM) ∧
      (∀ (M : Type 1) [AddCommGroup M] [NonUnitalModule Aᵐᵒᵖ M]
        (hM : IsNondegenerate Aᵐᵒᵖ M),
        RightSeparation hA hM ∧ RightEvaluationInjective hA hM) ∧
      EvaluationMonomorphisms.{0, 1} hA) := rfl


/-! Unequal universes: algebra in Type 1, module in Type 0. -/

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) → Prop :=
  @LeftSeparation.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) → Prop :=
  @LeftEvaluationInjective.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) → Prop :=
  @RightSeparation.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule Aᵐᵒᵖ M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate Aᵐᵒᵖ M) → Prop :=
  @RightEvaluationInjective.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    (hA : IsIdempotented A) → Prop := @EvaluationMonomorphisms.{1, 0}

example : Prop := BidualInjection.{1, 0}

example : BidualInjection.{1, 0} =
    (∀ (A : Type 1) [NonUnitalRing A] [Module ℂ A]
      [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (hA : IsIdempotented A),
      (∀ (M : Type 0) [AddCommGroup M] [NonUnitalModule A M]
        (hM : IsNondegenerate A M),
        LeftSeparation hA hM ∧ LeftEvaluationInjective hA hM) ∧
      (∀ (M : Type 0) [AddCommGroup M] [NonUnitalModule Aᵐᵒᵖ M]
        (hM : IsNondegenerate Aᵐᵒᵖ M),
        RightSeparation hA hM ∧ RightEvaluationInjective hA hM) ∧
      EvaluationMonomorphisms.{1, 0} hA) := rfl


end Langlands.Algebra.NonUnitalModuleBidualInjectionStatements
