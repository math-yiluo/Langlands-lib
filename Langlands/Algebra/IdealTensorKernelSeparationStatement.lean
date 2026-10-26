import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Noetherian.Basic

/-! # Mixed-scalar separation of ideal tensor kernels -/

universe u v w

open TensorProduct

namespace Langlands.Algebra

/-- The separatedness step in the local flatness argument, with explicit
kernel power bounds and a Jacobson-radical condition over the larger ring. -/
def IdealTensorKernelSeparationStatement : Prop :=
  ∀ (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M] (I : Ideal R),
    I.map (algebraMap R S) ≤ (⊥ : Ideal S).jacobson →
    (∀ (a : Ideal R) (n : ℕ),
      LinearMap.ker (LinearMap.lTensor M a.subtype) ≤
        (I ^ n • ⊤ : Submodule R (M ⊗[R] a))) →
    Module.Flat R M

end Langlands.Algebra
