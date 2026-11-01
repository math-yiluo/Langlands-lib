import Langlands.Algebra.NonUnitalModuleCornerEvaluationStatement

/-!
# Image, surjectivity and kernel annihilation for actual corner evaluation

The exact original-action aggregate in Renard I.3.2, with independent ring and
module universes and without unitality or nondegeneracy assumptions.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalModuleCornerEvaluationProof

open NonUnitalModuleCorner NonUnitalModuleCornerInduction
open NonUnitalModuleCornerEvaluation NonUnitalModuleIdempotentGenerated
open NonUnitalModuleCornerEvaluationStatement

universe uA uM

attribute [local instance] rightCornerModule cornerModule tensorModule

variable {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
  (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]

/-- The whole image, as an original stable additive subgroup. -/
theorem evaluation_image :
    NonUnitalModuleHom.rangeSubmodule (evaluation e M) = aeM e M := by
  apply le_antisymm
  · rintro m ⟨t, rfl⟩
    obtain ⟨q, rfl⟩ := NonUnitalModuleTensor.projection_surjective
      (Idempotent.Corner e) A (FixedPart e M) t
    refine TensorProduct.inductionOn q ?_ ?_
    · intro a z
      exact (aeM e M).smul_mem' a (fixedPart_le e z.property)
    · intro q r hq hr
      rw [map_add, map_add]
      exact (aeM e M).toAddSubgroup.add_mem hq hr
  · apply (aeM_le_iff e _).mpr
    intro m hm
    exact ⟨tmul e (e : A) ⟨m, hm⟩, evaluation_idempotent e M ⟨m, hm⟩⟩

/-- The exact criterion uses the specified action and the actual generated subgroup. -/
theorem evaluation_surjective_iff :
    Function.Surjective (evaluation e M) ↔ IsGeneratedByIdempotent e M := by
  change (∀ m : M, m ∈ NonUnitalModuleHom.rangeSubmodule (evaluation e M)) ↔
    ∀ m : M, m ∈ aeM e M
  rw [evaluation_image]

/-- Balancing against the corner unit inserts `e` on the right of a pure tensor. -/
theorem tmul_mul_idempotent (a : A) (z : FixedPart e M) :
    tmul e (a * e) z = tmul e a z := by
  simpa only [Idempotent.Corner.toAmbient_one, one_smul] using
    (tmul_balanced e (1 : Idempotent.Corner e) a z)

/-- The source idempotent action factors through evaluation on every pure tensor. -/
theorem idempotent_smul_tmul (a : A) (z : FixedPart e M) :
    (e : A) • tmul e a z =
      tmul e (e : A) (NonUnitalModuleCorner.projection e (a • z.val)) := by
  let c : Idempotent.Corner e :=
    ⟨(e : A) * a * e, (Idempotent.mem_corner_iff_exists e _).mpr ⟨a, rfl⟩⟩
  have hc : (e : A) * Idempotent.Corner.toAmbient e c =
      (e : A) * a * e :=
    ((Idempotent.mem_corner_iff e c.val).mp c.property).1
  have hz : (e : A) • z.val = z.val := z.property
  calc
    (e : A) • tmul e a z = tmul e ((e : A) * a) z :=
      tensorModule_smul_tmul e (e : A) a z
    _ = tmul e ((e : A) * a * e) z := (tmul_mul_idempotent e M _ z).symm
    _ = tmul e ((e : A) * Idempotent.Corner.toAmbient e c) z := by rw [hc]
    _ = tmul e (e : A) (c • z) := tmul_balanced e c (e : A) z
    _ = tmul e (e : A) (NonUnitalModuleCorner.projection e (a • z.val)) := by
      congr 1
      apply Subtype.ext
      change ((e : A) * a * e) • z.val = (e : A) • (a • z.val)
      rw [mul_smul, hz, mul_smul]

/-- Equality of additive maps extends the pure-tensor calculation to the whole quotient. -/
theorem idempotent_smul_tensor (t : Tensor e (FixedPart e M)) :
    (e : A) • t = tmul e (e : A)
      (NonUnitalModuleCorner.projection e (evaluation e M t)) := by
  let insertion : FixedPart e M →+ Tensor e (FixedPart e M) :=
    NonUnitalModuleTensor.biadditive (Idempotent.Corner e) A (FixedPart e M) (e : A)
  have h : NonUnitalModule.toEndHom (tensorModule e (FixedPart e M)) (e : A) =
      insertion.comp ((NonUnitalModuleCorner.projection e).comp
        (evaluation e M).toAddMonoidHom) := by
    apply NonUnitalModuleTensor.hom_ext (Idempotent.Corner e)
    intro a z
    exact idempotent_smul_tmul e M a z
  exact DFunLike.congr_fun h t

/-- The whole stable kernel is killed by every element of `eA` on the source tensor. -/
theorem evaluation_kernel_le_annihilator :
    NonUnitalModuleHom.kernelSubmodule (evaluation e M) ≤
      NonUnitalSubmodule.idempotentAnnihilator e (Tensor e (FixedPart e M)) := by
  apply (NonUnitalSubmodule.le_idempotentAnnihilator_iff _).mpr
  intro t ht
  have ht0 : evaluation e M t = 0 := ht
  rw [idempotent_smul_tensor e M, ht0, map_zero]
  exact NonUnitalModuleTensor.tmul_zero (Idempotent.Corner e) A (FixedPart e M) (e : A)

/-- The exact closed published aggregate, with independent ring and module universes. -/
theorem cornerEvaluation : CornerEvaluationStatement.{uA, uM} :=
  ⟨fun _ _ e M _ _ => evaluation_image e M,
    fun _ _ e M _ _ => evaluation_surjective_iff e M,
    fun _ _ e M _ _ => evaluation_kernel_le_annihilator e M⟩

namespace Checks

/-- Complete types retain both independent universes and no certificate argument. -/
example : CornerEvaluationStatement.{uA, uM} := @cornerEvaluation.{uA, uM}
example : CornerEvaluationStatement.{0, 1} := @cornerEvaluation.{0, 1}
example : CornerEvaluationStatement.{1, 0} := @cornerEvaluation.{1, 0}

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M],
    NonUnitalModuleHom.rangeSubmodule (evaluation e M) = aeM e M :=
  @evaluation_image.{uA, uM}

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M],
    Function.Surjective (evaluation e M) ↔ IsGeneratedByIdempotent e M :=
  @evaluation_surjective_iff.{uA, uM}

example : ∀ {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M],
    NonUnitalModuleHom.kernelSubmodule (evaluation e M) ≤
      NonUnitalSubmodule.idempotentAnnihilator e (Tensor e (FixedPart e M)) :=
  @evaluation_kernel_le_annihilator.{uA, uM}

section NamedActions

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

variable {B : Type uA} [bRing : NonUnitalRing B] (f : Idempotent B)
  (N : Type uM) [gN : AddCommGroup N] (h₀ : NonUnitalModule B N)
  [h₁ : NonUnitalModule B N]

local notation "F₀" => @FixedPart B bRing f N gN h₀
local notation "gF₀" => @fixedPartAddCommGroup B bRing f N gN h₀
local notation "mF₀" => @fixedPartModule B bRing f N gN h₀
local notation "T₀" => @Tensor B bRing f F₀ gF₀ mF₀
local notation "gT₀" => @tensorAddCommGroup B bRing f F₀ gF₀ mF₀
local notation "mT₀" => @tensorModule B bRing f F₀ gF₀ mF₀
local notation "ev₀" => @evaluation B bRing f N gN h₀

include h₁

example :
    @NonUnitalModuleHom.rangeSubmodule B bRing T₀ gT₀ mT₀ N gN h₀ ev₀ =
      @aeM B bRing f N gN h₀ :=
  @evaluation_image B bRing f N gN h₀

example : Function.Surjective ev₀ ↔ @IsGeneratedByIdempotent B bRing f N gN h₀ :=
  @evaluation_surjective_iff B bRing f N gN h₀

example :
    @NonUnitalModuleHom.kernelSubmodule B bRing T₀ gT₀ mT₀ N gN h₀ ev₀ ≤
      @NonUnitalSubmodule.idempotentAnnihilator B bRing f T₀ gT₀ mT₀ :=
  @evaluation_kernel_le_annihilator B bRing f N gN h₀

example (t : T₀) (ht : ev₀ t = 0) :
    ∀ b : B, (mT₀).toDistribSMul.toSMul.smul ((f : B) * b) t = 0 :=
  @evaluation_kernel_le_annihilator B bRing f N gN h₀ t ht

end NamedActions

/-- The zero idempotent has the exact zero-codomain criterion, without nonzero assumptions. -/
example :
    Function.Surjective (evaluation (⟨0, IsIdempotentElem.zero⟩ : Idempotent A) M) ↔
      ∀ m : M, m = 0 :=
  (evaluation_surjective_iff _ M).trans isGenerated_zero_idempotent_iff

/- The specified original zero action is supported directly by the proof. -/
omit [NonUnitalModule A M] in
example :
    letI : NonUnitalModule A M := NonUnitalModule.zero
    Function.Surjective (evaluation e M) ↔ ∀ m : M, m = 0 := by
  let : NonUnitalModule A M := NonUnitalModule.zero
  exact (evaluation_surjective_iff e M).trans (isGenerated_zero_action_iff e)

example [Subsingleton M] :
    NonUnitalModuleHom.rangeSubmodule (evaluation e M) = aeM e M ∧
    (Function.Surjective (evaluation e M) ↔ IsGeneratedByIdempotent e M) ∧
    NonUnitalModuleHom.kernelSubmodule (evaluation e M) ≤
      NonUnitalSubmodule.idempotentAnnihilator e (Tensor e (FixedPart e M)) :=
  ⟨evaluation_image e M, evaluation_surjective_iff e M, evaluation_kernel_le_annihilator e M⟩

example [Subsingleton A] :
    NonUnitalModuleHom.rangeSubmodule (evaluation e M) = aeM e M ∧
    (Function.Surjective (evaluation e M) ↔ IsGeneratedByIdempotent e M) ∧
    NonUnitalModuleHom.kernelSubmodule (evaluation e M) ≤
      NonUnitalSubmodule.idempotentAnnihilator e (Tensor e (FixedPart e M)) :=
  ⟨evaluation_image e M, evaluation_surjective_iff e M, evaluation_kernel_le_annihilator e M⟩

end Checks

end Langlands.Algebra.NonUnitalModuleCornerEvaluationProof
