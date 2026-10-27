import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

universe u v w z

namespace Langlands.Algebra

/-- The residue-tensor injection lifts to coefficients annihilated by a
power of the maximal ideal when the target is flat. -/
def ResidueTensorNilpotentInjectivityStatement : Prop :=
  ∀ (R : Type u) (A : Type v) (B : Type w) (C : Type z)
    [CommRing R] [IsLocalRing R]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C] (f : A →ₗ[R] B) (n : ℕ),
    Module.Flat R B →
    Function.Injective (LinearMap.lTensor (IsLocalRing.ResidueField R) f) →
    (∀ r ∈ IsLocalRing.maximalIdeal R ^ n, ∀ c : C, r • c = 0) →
    Function.Injective (LinearMap.lTensor C f)

end Langlands.Algebra
