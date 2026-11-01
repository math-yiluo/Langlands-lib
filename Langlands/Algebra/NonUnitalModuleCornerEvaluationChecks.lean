import Langlands.Algebra.NonUnitalModuleCornerEvaluation
import Mathlib.Algebra.Module.PUnit

/-!
# Interfaces and boundaries of actual corner evaluation

Internal checks for the complete declarations, named original structures and
independent universes; see the paired Markdown for their scope.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleCornerEvaluationChecks

open CategoryTheory
open NonUnitalModuleCorner NonUnitalModuleCornerInduction NonUnitalModuleCornerEvaluation

universe uA uM uN

attribute [local instance] rightCornerModule cornerModule tensorModule

section Interfaces

set_option linter.unusedVariables false

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M],
    A →+ FixedPart e M →+ M := @pairing

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (M : Type uM) [AddCommGroup M] [hM : NonUnitalModule A M],
    (fun a z => pairing e M a z) =
      fun a z => hM.toDistribSMul.toSMul.smul a z.val := @pairing_function

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (a : A) (z : FixedPart e M),
    pairing e M a z = a • z.val := @pairing_apply

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (c : Idempotent.Corner e) (a : A) (z : FixedPart e M),
    pairing e M (a * Idempotent.Corner.toAmbient e c) z =
      pairing e M a ((fixedPartModule e M).toSMul.smul c z) := @pairing_balancing

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M],
    NonUnitalModuleTensor.IsBalanced (Idempotent.Corner e) (pairing e M) :=
  @pairing_isBalanced

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (a₀ a : A) (z : FixedPart e M),
    pairing e M (a₀ * a) z = a₀ • pairing e M a z := @pairing_left_linear

/-- Complete unapplied interface, including the exact named tensor structures. -/
def evaluationInterface : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (M : Type uM) [AddCommGroup M] [hM : NonUnitalModule A M],
    @NonUnitalModuleHom A (Tensor e (FixedPart e M)) M _
      (tensorAddCommGroup e (FixedPart e M)) _
      (tensorModule e (FixedPart e M)) hM := @evaluation

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M],
    (evaluation e M).toAddMonoidHom =
      NonUnitalModuleTensor.lift (Idempotent.Corner e)
        (pairing e M) (pairing_isBalanced e M) := @evaluation_toAddMonoidHom

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (a : A) (z : FixedPart e M),
    evaluation e M (tmul e a z) = a • z.val := @evaluation_tmul

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M] (z : FixedPart e M),
    evaluation e M (tmul e (e : A) z) = z.val := @evaluation_idempotent

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (M : Type uM) [AddCommGroup M] [hM : NonUnitalModule A M]
    (a : A) (t : Tensor e (FixedPart e M)),
    evaluation e M ((tensorModule e (FixedPart e M)).toDistribSMul.toSMul.smul a t) =
      hM.toDistribSMul.toSMul.smul a (evaluation e M t) := @evaluation_map_smul

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (M : Type uM) [AddCommGroup M] [hM : NonUnitalModule A M]
    (F : @NonUnitalModuleHom A (Tensor e (FixedPart e M)) M _
      (tensorAddCommGroup e (FixedPart e M)) _
      (tensorModule e (FixedPart e M)) hM),
    (∀ a z, F (tmul e a z) = a • z.val) → F = evaluation e M := @evaluation_unique

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    {M : Type uM} {N : Type uN} [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule A M] [NonUnitalModule A N] (f : NonUnitalModuleHom A M N),
    f.comp (evaluation e M) =
      (evaluation e N).comp (inducedMap e (restrict e f)) := @evaluation_naturality

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    {M : Type uM} {N : Type uN} [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule A M] [NonUnitalModule A N] (f : NonUnitalModuleHom A M N),
    f.toAddMonoidHom.comp (evaluation e M).toAddMonoidHom =
      (evaluation e N).toAddMonoidHom.comp (inducedMap e (restrict e f)).toAddMonoidHom :=
  @evaluation_naturality_toAddMonoidHom

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    {M : Type uM} {N : Type uN} [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule A M] [NonUnitalModule A N] (f : NonUnitalModuleHom A M N)
    (t : Tensor e (FixedPart e M)),
    f (evaluation e M t) = evaluation e N (inducedMap e (restrict e f) t) :=
  @evaluation_naturality_apply

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A),
    NonUnitalModuleCorner.functor.{uA, max uA uM} e ⋙
        ambientFunctor.{uA, max uA uM} e ⟶
      𝟭 (NonUnitalModuleCat.{uA, max uA uM} A) := @ambientEvaluation

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (M : NonUnitalModuleCat.{uA, max uA uM} A),
    (ambientEvaluation e).app M = evaluation e M := @ambientEvaluation_app

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (M : NonUnitalModuleCat.{uA, max uA uM} A),
    ((ambientEvaluation e).app M).toAddMonoidHom =
      NonUnitalModuleTensor.lift (Idempotent.Corner e)
        (pairing e M) (pairing_isBalanced e M) := @ambientEvaluation_app_toAddMonoidHom

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (M : NonUnitalModuleCat.{uA, max uA uM} A) (a : A) (z : FixedPart e M),
    ((ambientEvaluation e).app M).toAddMonoidHom (tmul e a z) = a • z.val :=
  @ambientEvaluation_app_tmul

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    {M N : NonUnitalModuleCat.{uA, max uA uM} A} (f : M ⟶ N),
    f.comp ((ambientEvaluation e).app M) =
      ((ambientEvaluation e).app N).comp (inducedMap e (restrict e f)) :=
  @ambientEvaluation_naturality

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A),
    NonUnitalModuleCorner.nondegenerateFunctor.{uA, max uA uM} e ⋙
        NonUnitalModuleCornerInduction.nondegenerateFunctor.{uA, max uA uM} hA e ⟶
      𝟭 (NondegenerateModuleCat.{uA, max uA uM} A) := @nondegenerateEvaluation

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A),
    (nondegenerateEvaluation hA e).app M = ObjectProperty.homMk (evaluation e M.obj) :=
  @nondegenerateEvaluation_app

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A),
    ((nondegenerateEvaluation hA e).app M).hom = evaluation e M.obj :=
  @nondegenerateEvaluation_app_hom

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A),
    ((nondegenerateEvaluation hA e).app M).hom.toAddMonoidHom =
      NonUnitalModuleTensor.lift (Idempotent.Corner e)
        (pairing e M.obj) (pairing_isBalanced e M.obj) :=
  @nondegenerateEvaluation_app_toAddMonoidHom

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A) (a : A) (z : FixedPart e M.obj),
    ((nondegenerateEvaluation hA e).app M).hom.toAddMonoidHom (tmul e a z) = a • z.val :=
  @nondegenerateEvaluation_app_tmul

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A)
    {M N : NondegenerateModuleCat.{uA, max uA uM} A} (f : M ⟶ N),
    f.hom.comp ((nondegenerateEvaluation hA e).app M).hom =
      ((nondegenerateEvaluation hA e).app N).hom.comp (inducedMap e (restrict e f.hom)) :=
  @nondegenerateEvaluation_naturality

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A),
    (nondegenerateInclusion A).map ((nondegenerateEvaluation hA e).app M) =
      (ambientEvaluation e).app ((nondegenerateInclusion A).obj M) :=
  @NonUnitalModuleCornerEvaluation.inclusion_app

example : ∀ {A : Type uA} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A)
    {M N : NondegenerateModuleCat.{uA, max uA uM} A} (f : M ⟶ N),
    ((nondegenerateInclusion A).map f).comp
        ((nondegenerateInclusion A).map ((nondegenerateEvaluation hA e).app M)) =
      ((ambientEvaluation e).app N.obj).comp
        (inducedMap e (restrict e ((nondegenerateInclusion A).map f))) :=
  @NonUnitalModuleCornerEvaluation.inclusion_naturality

end Interfaces

section UnequalUniverses

set_option linter.unusedVariables false

example : ∀ {A : Type 0} [NonUnitalRing A] (e : Idempotent A)
    (M : Type 1) [AddCommGroup M] [hM : NonUnitalModule A M],
    @NonUnitalModuleHom A (Tensor e (FixedPart e M)) M _
      (tensorAddCommGroup e (FixedPart e M)) _
      (tensorModule e (FixedPart e M)) hM := @evaluation

example : ∀ {A : Type 1} [NonUnitalRing A] (e : Idempotent A)
    (M : Type 0) [AddCommGroup M] [hM : NonUnitalModule A M],
    @NonUnitalModuleHom A (Tensor e (FixedPart e M)) M _
      (tensorAddCommGroup e (FixedPart e M)) _
      (tensorModule e (FixedPart e M)) hM := @evaluation

example : ∀ {A : Type 0} [NonUnitalRing A] (e : Idempotent A)
    {M : Type 1} {N : Type 2} [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule A M] [NonUnitalModule A N] (f : NonUnitalModuleHom A M N),
    f.comp (evaluation e M) =
      (evaluation e N).comp (inducedMap e (restrict e f)) := @evaluation_naturality

example : ∀ {A : Type 2} [NonUnitalRing A] (e : Idempotent A)
    {M : Type 1} {N : Type 0} [AddCommGroup M] [AddCommGroup N]
    [NonUnitalModule A M] [NonUnitalModule A N] (f : NonUnitalModuleHom A M N),
    f.toAddMonoidHom.comp (evaluation e M).toAddMonoidHom =
      (evaluation e N).toAddMonoidHom.comp (inducedMap e (restrict e f)).toAddMonoidHom :=
  @evaluation_naturality_toAddMonoidHom

example : ∀ {A : Type 0} [NonUnitalRing A] (e : Idempotent A),
    NonUnitalModuleCorner.functor.{0, 1} e ⋙ ambientFunctor.{0, 1} e ⟶
      𝟭 (NonUnitalModuleCat.{0, 1} A) := @ambientEvaluation

example : ∀ {A : Type 1} [NonUnitalRing A] (e : Idempotent A),
    NonUnitalModuleCorner.functor.{1, 1} e ⋙ ambientFunctor.{1, 1} e ⟶
      𝟭 (NonUnitalModuleCat.{1, 1} A) := @ambientEvaluation.{1, 0}

example : ∀ {A : Type 0} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A),
    NonUnitalModuleCorner.nondegenerateFunctor.{0, 1} e ⋙
        NonUnitalModuleCornerInduction.nondegenerateFunctor.{0, 1} hA e ⟶
      𝟭 (NondegenerateModuleCat.{0, 1} A) := @nondegenerateEvaluation

example : ∀ {A : Type 1} [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A),
    NonUnitalModuleCorner.nondegenerateFunctor.{1, 1} e ⋙
        NonUnitalModuleCornerInduction.nondegenerateFunctor.{1, 1} hA e ⟶
      𝟭 (NondegenerateModuleCat.{1, 1} A) := @nondegenerateEvaluation.{1, 0}

end UnequalUniverses

section CompetingActions

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

variable {A : Type uA} [aRing : NonUnitalRing A] (e : Idempotent A)
  (M : Type uM) [gM : AddCommGroup M] (h₀ : NonUnitalModule A M)
  [h₁ : NonUnitalModule A M]

local notation "F₀" => @FixedPart A aRing e M gM h₀
local notation "gF₀" => @fixedPartAddCommGroup A aRing e M gM h₀
local notation "mF₀" => @fixedPartModule A aRing e M gM h₀
local notation "Q₀" => @Tensor A aRing e
  (@FixedPart A aRing e M gM h₀) (@fixedPartAddCommGroup A aRing e M gM h₀)
  (@fixedPartModule A aRing e M gM h₀)
local notation "gQ₀" => @tensorAddCommGroup A aRing e
  (@FixedPart A aRing e M gM h₀) (@fixedPartAddCommGroup A aRing e M gM h₀)
  (@fixedPartModule A aRing e M gM h₀)
local notation "mQ₀" => @tensorModule A aRing e
  (@FixedPart A aRing e M gM h₀) (@fixedPartAddCommGroup A aRing e M gM h₀)
  (@fixedPartModule A aRing e M gM h₀)

variable [otherRight : NonUnitalModule (Idempotent.Corner e)ᵐᵒᵖ A]
  [otherFixed : @Module (Idempotent.Corner e)
    (@FixedPart A aRing e M gM h₀) (Idempotent.Corner.ring e).toSemiring
    (@fixedPartAddCommGroup A aRing e M gM h₀).toAddCommMonoid]
  [otherOriginalFixed : @NonUnitalModule (Idempotent.Corner e)
    (@FixedPart A aRing e M gM h₀) (Idempotent.Corner.ring e).toNonUnitalRing
    (@fixedPartAddCommGroup A aRing e M gM h₀)]
  [otherTensor : @NonUnitalModule A
    (@Tensor A aRing e (@FixedPart A aRing e M gM h₀)
      (@fixedPartAddCommGroup A aRing e M gM h₀) (@fixedPartModule A aRing e M gM h₀))
    aRing
    (@tensorAddCommGroup A aRing e (@FixedPart A aRing e M gM h₀)
      (@fixedPartAddCommGroup A aRing e M gM h₀) (@fixedPartModule A aRing e M gM h₀))]

include h₁ otherRight otherFixed otherOriginalFixed otherTensor

example : (inferInstance : NonUnitalModule A M) = h₁ := rfl
example : (inferInstance : NonUnitalModule (Idempotent.Corner e)ᵐᵒᵖ A) = otherRight := rfl

theorem competingFixedModuleInstance :
    (inferInstance : @Module (Idempotent.Corner e)
      (@FixedPart A aRing e M gM h₀) (Idempotent.Corner.ring e).toSemiring
      (@fixedPartAddCommGroup A aRing e M gM h₀).toAddCommMonoid) = otherFixed := rfl

theorem competingFixedOriginalInstance :
    (inferInstance : @NonUnitalModule (Idempotent.Corner e)
      (@FixedPart A aRing e M gM h₀) (Idempotent.Corner.ring e).toNonUnitalRing
      (@fixedPartAddCommGroup A aRing e M gM h₀)) = otherOriginalFixed := rfl

theorem competingTensorInstance :
    (inferInstance : @NonUnitalModule A
      (@Tensor A aRing e (@FixedPart A aRing e M gM h₀)
        (@fixedPartAddCommGroup A aRing e M gM h₀) (@fixedPartModule A aRing e M gM h₀))
      aRing
      (@tensorAddCommGroup A aRing e (@FixedPart A aRing e M gM h₀)
        (@fixedPartAddCommGroup A aRing e M gM h₀) (@fixedPartModule A aRing e M gM h₀))) =
      otherTensor := rfl

example : A →+ @AddMonoidHom F₀ M (gF₀).toAddZero _ :=
  @pairing A _ e M _ h₀

example (a : A) (z : F₀) :
    @pairing A _ e M _ h₀ a z = h₀.toDistribSMul.toSMul.smul a z.val := rfl

example : @NonUnitalModuleHom A Q₀ M _ gQ₀ _ mQ₀ h₀ :=
  @evaluation A _ e M _ h₀

example :
    letI := gF₀
    letI := mF₀
    letI := rightCornerModule e
    letI := cornerModule e F₀
    @NonUnitalModuleHom.toAddMonoidHom A Q₀ M aRing gQ₀ gM mQ₀ h₀
      (@evaluation A aRing e M gM h₀) =
      NonUnitalModuleTensor.lift (Idempotent.Corner e)
        (@pairing A _ e M _ h₀) (@pairing_isBalanced A _ e M _ h₀) := rfl

example (a : A) (z : F₀) :
    (@evaluation A _ e M _ h₀) (@tmul A _ e F₀ gF₀ mF₀ a z) =
      h₀.toDistribSMul.toSMul.smul a z.val :=
  @evaluation_tmul A _ e M _ h₀ a z

example (a : A) (t : Q₀) :
    (@evaluation A _ e M _ h₀) ((mQ₀).toDistribSMul.toSMul.smul a t) =
      h₀.toDistribSMul.toSMul.smul a ((@evaluation A _ e M _ h₀) t) :=
  @evaluation_map_smul A _ e M _ h₀ a t

end CompetingActions

section BoundaryCases

variable {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
  (M : Type uM) [AddCommGroup M] [hM : NonUnitalModule A M]

example [Subsingleton M] : evaluation e M = 0 :=
  NonUnitalModuleHom.ext (fun _ => Subsingleton.elim _ _)

example [Subsingleton A] : evaluation e M = 0 := by
  apply Eq.symm
  apply evaluation_unique
  intro a z
  change (0 : M) = a • z.val
  rw [Subsingleton.elim a 0, NonUnitalModule.zero_smul]

example (he : (e : A) = 0) : evaluation e M = 0 := by
  apply Eq.symm
  apply evaluation_unique
  intro a z
  have hz : z.val = 0 := by
    have hz := z.property
    change (e : A) • z.val = z.val at hz
    rw [he, NonUnitalModule.zero_smul] at hz
    exact hz.symm
  change (0 : M) = a • z.val
  rw [hz, smul_zero]

example : evaluation (⟨0, IsIdempotentElem.zero⟩ : Idempotent A) M = 0 := by
  apply Eq.symm
  apply evaluation_unique
  intro a z
  have hz : z.val = 0 := by
    have hz := z.property
    change (0 : A) • z.val = z.val at hz
    rw [NonUnitalModule.zero_smul] at hz
    exact hz.symm
  change (0 : M) = a • z.val
  rw [hz, smul_zero]

omit hM in
example :
    letI : NonUnitalModule A M := NonUnitalModule.zero
    evaluation e M = 0 := by
  let : NonUnitalModule A M := NonUnitalModule.zero
  apply Eq.symm
  apply evaluation_unique
  intro a z
  rfl

example :
    letI : NonUnitalModule A PUnit.{uM + 1} := NonUnitalModule.zero
    @NonUnitalModuleHom A (Tensor e (FixedPart e PUnit.{uM + 1})) PUnit _
      (tensorAddCommGroup e (FixedPart e PUnit)) _
      (tensorModule e (FixedPart e PUnit)) NonUnitalModule.zero := by
  letI : NonUnitalModule A PUnit.{uM + 1} := NonUnitalModule.zero
  exact evaluation e PUnit

example :
    letI : NonUnitalModule ℤ ℤ := NonUnitalModule.zero
    let e₁ : Idempotent ℤ := ⟨1, IsIdempotentElem.one⟩
    evaluation e₁ ℤ = 0 := by
  let : NonUnitalModule ℤ ℤ := NonUnitalModule.zero
  apply Eq.symm
  apply evaluation_unique
  intro a z
  rfl

end BoundaryCases

end Langlands.Algebra.NonUnitalModuleCornerEvaluationChecks
