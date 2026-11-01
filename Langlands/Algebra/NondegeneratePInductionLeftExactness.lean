import Langlands.Algebra.NondegenerateInductionExactnessStatements
import Langlands.Algebra.NondegenerateModuleExactnessProof

/-!
# Left exactness of the actual pseudo-forgetful functor

The fixed regular-source Hom preserves concrete kernels by taking the
pointwise subtype lift. The published inclusion and nondegenerate-part
exactness then give the full left sequence condition.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra

universe uA uB v

namespace RenardHomFunctors

open NondegenerateHomFunctor

variable {A : Type uA} {B : Type uB} [NonUnitalRing A] [NonUnitalRing B]
  [NonUnitalModule Aᵐᵒᵖ B]

local instance : NonUnitalModule B B := NonUnitalModule.regular B

variable (hBA : ActionsCommute B A B)

/-- Lift a family of actual `B`-linear maps pointwise into the concrete kernel. -/
private def pseudoKernelLift {M N : NonUnitalModuleCat.{uB, v} B}
    (f : M ⟶ N) {Q : NonUnitalModuleCat.{uA, max uB v} A}
    (k : Q ⟶ (ambientFunctor hBA).obj M)
    (hk : k ≫ (ambientFunctor hBA).map f = 0) :
    Q ⟶ (ambientFunctor hBA).obj (NonUnitalModuleCat.concreteKernel f) where
  toFun q := f.kernelLift (k.toAddMonoidHom q) (by
    apply NonUnitalModuleHom.ext
    intro b
    exact congrArg (fun t : Q ⟶ (ambientFunctor hBA).obj N =>
      (t.toAddMonoidHom q).toAddMonoidHom b) hk)
  map_zero' := by
    apply NonUnitalModuleHom.ext
    intro b
    apply Subtype.ext
    exact congrArg (fun t : NonUnitalModuleHom B B M => t b) k.map_zero
  map_add' q r := by
    apply NonUnitalModuleHom.ext
    intro b
    apply Subtype.ext
    exact congrArg (fun t : NonUnitalModuleHom B B M => t b) (k.map_add q r)
  map_smul' a q := by
    apply NonUnitalModuleHom.ext
    intro b
    apply Subtype.ext
    exact congrArg (fun t : NonUnitalModuleHom B B M => t b) (k.map_smul a q)

/-- The fixed actual regular-source Hom preserves each kernel, without a
restriction on the source carrier universe. -/
theorem pseudoAmbient_preservesKernel {M N : NonUnitalModuleCat.{uB, v} B}
    (f : M ⟶ N) :
    PreservesLimit (parallelPair f 0) (ambientFunctor hBA) := by
  apply preservesLimit_of_preserves_limit_cone (NonUnitalModuleCat.concreteKernelIsLimit f)
  apply (KernelFork.isLimitMapConeEquiv _ (ambientFunctor hBA)).2
  refine KernelFork.IsLimit.ofι _
    ((NonUnitalModuleCat.concreteKernelFork f).map_condition (ambientFunctor hBA))
    (fun k hk => pseudoKernelLift hBA f k hk) ?_ ?_
  · intro Q k hk
    apply NonUnitalModuleHom.ext
    intro q
    apply NonUnitalModuleHom.ext
    intro b
    rfl
  · intro Q k hk l hl
    apply NonUnitalModuleHom.ext
    intro q
    apply NonUnitalModuleHom.ext
    intro b
    apply Subtype.ext
    exact congrArg (fun t : Q ⟶ (ambientFunctor hBA).obj M =>
      (t.toAddMonoidHom q).toAddMonoidHom b) hl

/-- Finite limits for the actual ambient Hom in the independent carrier universe. -/
theorem pseudoAmbient_preservesFiniteLimits :
    PreservesFiniteLimits (ambientFunctor.{uB, uA, uB, v} hBA) := by
  let : ∀ {M N : NonUnitalModuleCat.{uB, v} B} (f : M ⟶ N),
      PreservesLimit (parallelPair f 0) (ambientFunctor hBA) :=
    fun f => pseudoAmbient_preservesKernel hBA f
  exact Functor.preservesFiniteLimits_of_preservesKernels _

/-- Renard's full left sequence condition for the published pseudo-F. -/
theorem pseudoF_sequenceLeftExact (hA : IsIdempotented A) (hB : IsIdempotented B) :
    letI := NondegenerateModuleCat.abelian.{uB, v} B hB
    letI := NondegenerateModuleCat.abelian.{uA, max uB v} A hA
    Langlands.Renard.SequenceLeftExact (pseudoF.{uA, uB, v} hBA hA) := by
  let := NondegenerateModuleCat.abelian.{uB, v} B hB
  let := NondegenerateModuleCat.abelian.{uA, max uB v} A hA
  let := nondegenerateInclusion_preservesHomology.{uB, v} hB
  let : PreservesFiniteLimits (nondegenerateInclusion.{uB, v} B) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  let := pseudoAmbient_preservesFiniteLimits.{uA, uB, v} hBA
  let := nondegeneratePartFunctor_preservesHomology.{uA, max uB v} hA
  let : PreservesFiniteLimits (nondegeneratePartFunctor.{uA, max uB v} hA) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  apply (Langlands.Renard.sequenceLeftExactFiniteLimits _).2
  rw [pseudoF_eq_composite]
  infer_instance

end RenardHomFunctors

end Langlands.Algebra
