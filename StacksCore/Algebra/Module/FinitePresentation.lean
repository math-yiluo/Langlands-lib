module

public import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-! # Finitely presented modules -/

@[expose] public section

variable {R M1 M2 M3 : Type*} [Ring R] [AddCommGroup M1] [AddCommGroup M2] [AddCommGroup M3]
  [Module R M1] [Module R M2] [Module R M3] (f : M1 →ₗ[R] M2) (g : M2 →ₗ[R] M3)
  (hfg : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g)

/-- `M1` is isomorphic to the kernel of `g` when `f` is injective and `f, g` are exact. -/
private noncomputable def kerEquivOfExact : M1 ≃ₗ[R] LinearMap.ker g :=
  (LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ (LinearMap.exact_iff.1 hfg).symm)

include hfg hf hg in
@[stacks 0519 "2"]
lemma Module.FinitePresentation.of_exact_fst [Module.FinitePresentation R M1]
    [Module.FinitePresentation R M3] :
    Module.FinitePresentation R M2 := by
  have : Module.FinitePresentation R (LinearMap.ker g) := .of_equiv (kerEquivOfExact f g hfg hf)
  exact Module.finitePresentation_of_ker g hg
