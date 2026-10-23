import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.Dual.Defs

/-! Internal algebraic target for the dimension-one step of Whittaker heredity. -/

namespace Langlands.LinearAlgebra

universe uk ui uv

/-- The full algebraic dual of a finite indexed tensor product has a nonzero
spanning element exactly when each factor dual does. -/
def DualTensorOneDimensionalStatement : Prop :=
  ∀ (k : Type uk) [Field k] (ι : Type ui) [Finite ι]
    (V : ι → Type uv) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)],
    (∃ ℓ : Module.Dual k (PiTensorProduct k V), ℓ ≠ 0 ∧
      ∀ ℓ', ∃ c : k, ℓ' = c • ℓ) ↔
    ∀ i, ∃ ℓ : Module.Dual k (V i), ℓ ≠ 0 ∧
      ∀ ℓ', ∃ c : k, ℓ' = c • ℓ

end Langlands.LinearAlgebra
