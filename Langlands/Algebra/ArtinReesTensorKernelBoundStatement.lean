import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Noetherian.Basic

/-! # Artin–Rees bounds for ideal tensor kernels -/

universe u v

open scoped TensorProduct

namespace Langlands.Algebra

/-- The arbitrarily deep ideal-power bound extracted from the Artin–Rees
step in the proof of Stacks Project Lemma 10.99.7 (tag 00MK). -/
def ArtinReesTensorKernelBoundStatement : Prop :=
  ∀ (R : Type u) (M : Type v)
    [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R),
    (∀ (J : Ideal R) (n : ℕ), I ^ n ≤ J →
      Function.Injective (LinearMap.lTensor M J.subtype)) →
    ∀ (a : Ideal R) (n : ℕ),
      LinearMap.ker (LinearMap.lTensor M a.subtype) ≤
        (I ^ n • ⊤ : Submodule R (M ⊗[R] a))

end Langlands.Algebra
