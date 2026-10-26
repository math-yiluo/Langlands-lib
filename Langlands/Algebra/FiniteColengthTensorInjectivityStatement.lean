import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-! # Tensor injectivity for ideals containing maximal-ideal powers -/

universe u v

namespace Langlands.Algebra

/-- The finite-colength tensor-injectivity step used in the proof of
Stacks Project Lemma 10.99.7 (00MK), derived from Lemma 10.99.6 (00MJ). -/
def FiniteColengthTensorInjectivityStatement : Prop :=
  ∀ (R : Type u) (M : Type v)
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M],
    Function.Injective (LinearMap.lTensor M (IsLocalRing.maximalIdeal R).subtype) →
    ∀ (J : Ideal R) (n : ℕ), (IsLocalRing.maximalIdeal R) ^ n ≤ J →
      Function.Injective (LinearMap.lTensor M J.subtype)

end Langlands.Algebra
