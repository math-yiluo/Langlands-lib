import Langlands.Algebra.NonUnitalModuleCornerEvaluation
import Langlands.Algebra.NonUnitalModuleIdempotentGenerated
import Langlands.Algebra.IdempotentAnnihilatorQuotient.NamedCarrier

/-!
# Image and kernel statements for actual corner evaluation

Closed targets for Renard (9 July 2026), I.3.2, printed pp.21–22 /
PDF pp.27–28. The arbitrary-ring image criterion is an internal generalization.
These declarations state the assertions; they do not prove them.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalModuleCornerEvaluationStatement

open NonUnitalModuleCorner NonUnitalModuleCornerInduction
open NonUnitalModuleCornerEvaluation NonUnitalModuleIdempotentGenerated

universe uA uM

attribute [local instance] rightCornerModule cornerModule tensorModule

/-- The whole original-action image is the actual additive generated submodule. -/
def EvaluationImageStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (e : Idempotent A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M],
    letI := fixedPartAddCommGroup e M
    letI := fixedPartModule e M
    letI := tensorAddCommGroup e (FixedPart e M)
    letI := tensorModule e (FixedPart e M)
    NonUnitalModuleHom.rangeSubmodule (evaluation e M) = aeM e M

/-- Surjectivity of the actual evaluation is equivalent to actual generatedness. -/
def EvaluationSurjectivityStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (e : Idempotent A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M],
    letI := fixedPartAddCommGroup e M
    letI := fixedPartModule e M
    letI := tensorAddCommGroup e (FixedPart e M)
    letI := tensorModule e (FixedPart e M)
    Function.Surjective (evaluation e M) ↔ IsGeneratedByIdempotent e M

/-- Every `e*a` annihilates every kernel vector under the named tensor action. -/
def EvaluationKernelAnnihilationStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (e : Idempotent A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M],
    letI := fixedPartAddCommGroup e M
    letI := fixedPartModule e M
    letI := tensorAddCommGroup e (FixedPart e M)
    letI := tensorModule e (FixedPart e M)
    NonUnitalModuleHom.kernelSubmodule (evaluation e M) ≤
      NonUnitalSubmodule.idempotentAnnihilator e (Tensor e (FixedPart e M))

/-- The closed aggregate target for the separate exact-proof successor. -/
def CornerEvaluationStatement : Prop :=
  EvaluationImageStatement.{uA, uM} ∧
  EvaluationSurjectivityStatement.{uA, uM} ∧
  EvaluationKernelAnnihilationStatement.{uA, uM}

/-! Reproducible interface checks. No proof of the target is supplied below. -/

namespace Checks

/-- Each complete unapplied declaration has type `Prop`, with no term parameters. -/
example : Prop := @EvaluationImageStatement.{uA, uM}
example : Prop := @EvaluationSurjectivityStatement.{uA, uM}
example : Prop := @EvaluationKernelAnnihilationStatement.{uA, uM}
example : Prop := @CornerEvaluationStatement.{uA, uM}

example : Prop := @EvaluationImageStatement.{0, 1}
example : Prop := @EvaluationSurjectivityStatement.{0, 1}
example : Prop := @EvaluationKernelAnnihilationStatement.{0, 1}
example : Prop := @CornerEvaluationStatement.{0, 1}
example : Prop := @EvaluationImageStatement.{1, 0}
example : Prop := @EvaluationSurjectivityStatement.{1, 0}
example : Prop := @EvaluationKernelAnnihilationStatement.{1, 0}
example : Prop := @CornerEvaluationStatement.{1, 0}

section NamedActions

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

variable {A : Type uA} [aRing : NonUnitalRing A] (e : Idempotent A)
  (M : Type uM) [gM : AddCommGroup M] (h₀ : NonUnitalModule A M)
  [h₁ : NonUnitalModule A M]

local notation "F₀" => @FixedPart A aRing e M gM h₀
local notation "gF₀" => @fixedPartAddCommGroup A aRing e M gM h₀
local notation "mF₀" => @fixedPartModule A aRing e M gM h₀
local notation "T₀" => @Tensor A aRing e F₀ gF₀ mF₀
local notation "gT₀" => @tensorAddCommGroup A aRing e F₀ gF₀ mF₀
local notation "mT₀" => @tensorModule A aRing e F₀ gF₀ mF₀
local notation "ev₀" => @evaluation A aRing e M gM h₀

include h₁

/-- The closed image target can select `h₀` even in the presence of `h₁`. -/
example (h : EvaluationImageStatement.{uA, uM}) :
    @NonUnitalModuleHom.rangeSubmodule A aRing T₀ gT₀ mT₀ M gM h₀ ev₀ =
      @aeM A aRing e M gM h₀ :=
  @h A aRing e M gM h₀

example (h : EvaluationSurjectivityStatement.{uA, uM}) :
    Function.Surjective ev₀ ↔ @IsGeneratedByIdempotent A aRing e M gM h₀ :=
  @h A aRing e M gM h₀

example (h : EvaluationKernelAnnihilationStatement.{uA, uM}) :
    @NonUnitalModuleHom.kernelSubmodule A aRing T₀ gT₀ mT₀ M gM h₀ ev₀ ≤
      @NonUnitalSubmodule.idempotentAnnihilator A aRing e T₀ gT₀ mT₀ :=
  @h A aRing e M gM h₀

/-- Membership means annihilation by every `e*a` under exactly `mT₀`. -/
example (t : T₀) :
    t ∈ @NonUnitalSubmodule.idempotentAnnihilator A aRing e T₀ gT₀ mT₀ ↔
      ∀ a : A, (mT₀).toDistribSMul.toSMul.smul ((e : A) * a) t = 0 :=
  Iff.rfl

end NamedActions

/-- The entire kernel assertion unfolds to the required original-action formula. -/
example :
    EvaluationKernelAnnihilationStatement.{uA, uM} =
      (∀ (A : Type uA) [NonUnitalRing A] (e : Idempotent A)
        (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
        (t : Tensor e (FixedPart e M)),
        evaluation e M t = 0 →
          ∀ a : A,
            (tensorModule e (FixedPart e M)).toDistribSMul.toSMul.smul
              ((e : A) * a) t = 0) := rfl

section Boundaries

variable {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
  (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]

/-- These are specializations of a hypothetical aggregate proof, not such a proof. -/
example (h : CornerEvaluationStatement.{uA, uM}) :
    let e₀ : Idempotent A := ⟨0, IsIdempotentElem.zero⟩
    NonUnitalModuleHom.rangeSubmodule (evaluation e₀ M) = aeM e₀ M ∧
    (Function.Surjective (evaluation e₀ M) ↔ IsGeneratedByIdempotent e₀ M) ∧
    NonUnitalModuleHom.kernelSubmodule (evaluation e₀ M) ≤
      NonUnitalSubmodule.idempotentAnnihilator e₀ (Tensor e₀ (FixedPart e₀ M)) :=
  ⟨h.1 A _ M, h.2.1 A _ M, h.2.2 A _ M⟩

example (h : CornerEvaluationStatement.{uA, uM}) :
    letI : NonUnitalModule A M := NonUnitalModule.zero
    NonUnitalModuleHom.rangeSubmodule (evaluation e M) = aeM e M ∧
    (Function.Surjective (evaluation e M) ↔ IsGeneratedByIdempotent e M) ∧
    NonUnitalModuleHom.kernelSubmodule (evaluation e M) ≤
      NonUnitalSubmodule.idempotentAnnihilator e (Tensor e (FixedPart e M)) := by
  let : NonUnitalModule A M := NonUnitalModule.zero
  exact ⟨h.1 A e M, h.2.1 A e M, h.2.2 A e M⟩

example [Subsingleton M] (h : CornerEvaluationStatement.{uA, uM}) :
    NonUnitalModuleHom.rangeSubmodule (evaluation e M) = aeM e M ∧
    (Function.Surjective (evaluation e M) ↔ IsGeneratedByIdempotent e M) ∧
    NonUnitalModuleHom.kernelSubmodule (evaluation e M) ≤
      NonUnitalSubmodule.idempotentAnnihilator e (Tensor e (FixedPart e M)) :=
  ⟨h.1 A e M, h.2.1 A e M, h.2.2 A e M⟩

example [Subsingleton A] (h : CornerEvaluationStatement.{uA, uM}) :
    NonUnitalModuleHom.rangeSubmodule (evaluation e M) = aeM e M ∧
    (Function.Surjective (evaluation e M) ↔ IsGeneratedByIdempotent e M) ∧
    NonUnitalModuleHom.kernelSubmodule (evaluation e M) ≤
      NonUnitalSubmodule.idempotentAnnihilator e (Tensor e (FixedPart e M)) :=
  ⟨h.1 A e M, h.2.1 A e M, h.2.2 A e M⟩

end Boundaries
end Checks

end Langlands.Algebra.NonUnitalModuleCornerEvaluationStatement
