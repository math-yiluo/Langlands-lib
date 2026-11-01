import Langlands.Algebra.NonUnitalModuleBidualInjectionStatements
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Separation and the canonical bidual injection

Renard (9 July 2026), I.4.1 corollary, printed p.23 / PDF p.29. A nonzero vector
is detected by a full complex functional `λ`; composing `λ` with an idempotent
fixing the vector gives `λ · e` in the actual nondegenerate dual, still detecting it.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleBidualInjectionProof

open CategoryTheory MulOpposite NonUnitalModuleDual NonUnitalModuleRightBidual
  NonUnitalModuleBidualInjectionStatements

universe uA uM

section Left

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M)

/-- Composing a full functional with an original idempotent lands in the actual dual. -/
theorem idempotent_smul_mem (ψ : FullDual hA hM) (e : Idempotent A) :
    letI := fullAction hA hM
    op (e : A) • ψ ∈ nondegeneratePart hA.op (FullDual hA hM) := by
  let _ := fullAction hA hM
  refine (mem_dual_iff hA hM _).2 ⟨e, fun m => ?_⟩
  change ψ ((e : A) • (e : A) • m) = ψ ((e : A) • m)
  rw [← mul_smul, e.property.eq]

/-- Renard's corrected functional `λ · e`, as an element of the actual dual. -/
def idempotentCut (ψ : FullDual hA hM) (e : Idempotent A) : Dual hA hM :=
  letI := fullAction hA hM
  ⟨op (e : A) • ψ, idempotent_smul_mem hA hM ψ e⟩

@[simp] theorem idempotentCut_apply (ψ : FullDual hA hM) (e : Idempotent A) (m : M) :
    (idempotentCut hA hM ψ e).val m = ψ ((e : A) • m) := rfl

/-- If `e` fixes `m`, then `λ · e` takes the same value as `λ` at `m`. -/
theorem idempotentCut_apply_of_fixed (ψ : FullDual hA hM) (e : Idempotent A) {m : M}
    (he : (e : A) • m = m) : (idempotentCut hA hM ψ e).val m = ψ m := by
  rw [idempotentCut_apply, he]

/-- The full complex dual of the recovered scalar module separates points. -/
theorem exists_fullDual_ne_zero {m : M} (hm : m ≠ 0) :
    ∃ ψ : FullDual hA hM, ψ m ≠ 0 := by
  let _ := NondegenerateScalars.complexModule hA hM
  exact Module.Projective.exists_dual_ne_zero ℂ hm

/-- Every nonzero original vector is detected by the actual nondegenerate dual. -/
theorem leftSeparation : LeftSeparation hA hM := by
  intro m hm
  obtain ⟨ψ, hψ⟩ := exists_fullDual_ne_zero hA hM hm
  obtain ⟨e, he⟩ := hM m
  exact ⟨idempotentCut hA hM ψ e, by rwa [idempotentCut_apply_of_fixed hA hM ψ e he]⟩

/-- Vectors on which every functional of the actual dual agrees are equal. -/
theorem eq_of_forall_dual_apply_eq {m n : M} (h : ∀ φ : Dual hA hM, φ.val m = φ.val n) :
    m = n := by
  let _ := NondegenerateScalars.complexModule hA hM
  by_contra hmn
  obtain ⟨φ, hφ⟩ := leftSeparation hA hM (m - n) (sub_ne_zero.2 hmn)
  exact hφ (by rw [φ.val.map_sub, h φ, sub_self])

/-- The exact published canonical evaluation is injective. -/
theorem evaluation_injective :
    letI := bidualAction hA hM
    Function.Injective (evaluation hA hM) := by
  let _ := bidualAction hA hM
  intro m n h
  exact eq_of_forall_dual_apply_eq hA hM fun φ =>
    congrArg (fun Φ : Bidual hA hM => Φ.val φ) h

/-- Its recovered complex-linear presentation has the same underlying map. -/
theorem evaluationLinear_injective :
    letI := bidualAction hA hM
    letI := NondegenerateScalars.complexModule hA hM
    letI := NondegenerateScalars.complexModule hA (bidual_isNondegenerate hA hM)
    Function.Injective (evaluationLinear hA hM) := by
  let _ := bidualAction hA hM
  exact evaluation_injective hA hM

theorem leftEvaluationInjective : LeftEvaluationInjective hA hM :=
  ⟨evaluation_injective hA hM, evaluationLinear_injective hA hM⟩

end Left

section Right

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule Aᵐᵒᵖ M]
  (hA : IsIdempotented A) (hM : IsNondegenerate Aᵐᵒᵖ M)

/-- Right separation is the left argument over the opposite algebra, with `Dual hA.op hM`. -/
theorem rightSeparation : RightSeparation hA hM :=
  leftSeparation hA.op hM

/-- The exact right evaluation, into the actual `RightBidual`, is injective. -/
theorem rightEvaluation_injective :
    letI := rightBidualAction hA hM
    Function.Injective (rightEvaluation hA hM) := by
  let _ := rightBidualAction hA hM
  intro m n h
  exact eq_of_forall_dual_apply_eq hA.op hM fun φ =>
    congrArg (fun Φ : RightBidual hA hM => Φ.val φ) h

theorem rightEvaluationLinear_injective :
    letI := rightBidualAction hA hM
    letI := NondegenerateScalars.complexModule hA.op hM
    letI := NondegenerateScalars.complexModule hA.op (rightBidual_isNondegenerate hA hM)
    Function.Injective (rightEvaluationLinear hA hM) := by
  let _ := rightBidualAction hA hM
  exact rightEvaluation_injective hA hM

theorem rightEvaluationInjective : RightEvaluationInjective hA hM :=
  ⟨rightEvaluation_injective hA hM, rightEvaluationLinear_injective hA hM⟩

end Right

section Categorical

/-- A morphism of nondegenerate modules with injective underlying map is a monomorphism. -/
theorem mono_of_injective {A : Type uA} [NonUnitalRing A]
    {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N)
    (hf : Function.Injective f.hom.toAddMonoidHom) : Mono f := by
  refine ⟨fun {P} g h w => ?_⟩
  apply ObjectProperty.hom_ext
  apply NonUnitalModuleHom.ext
  intro m
  apply hf
  exact congrArg (fun k : P ⟶ N => k.hom.toAddMonoidHom m) w

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]

theorem evaluationMonomorphisms (hA : IsIdempotented A) :
    EvaluationMonomorphisms.{uA, uM} hA :=
  ⟨fun M => mono_of_injective _ (evaluation_injective hA M.property),
    fun M => mono_of_injective _ (rightEvaluation_injective hA M.property)⟩

end Categorical

/-- Renard I.4.1: separation and the canonical bidual injection on both sides. -/
theorem bidualInjection : BidualInjection.{uA, uM} := fun _ _ _ _ _ hA =>
  ⟨fun _ _ _ hM => ⟨leftSeparation hA hM, leftEvaluationInjective hA hM⟩,
    fun _ _ _ hM => ⟨rightSeparation hA hM, rightEvaluationInjective hA hM⟩,
    evaluationMonomorphisms hA⟩

end Langlands.Algebra.NonUnitalModuleBidualInjectionProof
