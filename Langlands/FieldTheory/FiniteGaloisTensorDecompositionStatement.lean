import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Statement: the explicit decomposition of `L ⊗[k] L` for a finite Galois extension -/

namespace Langlands.FieldTheory

universe u

open scoped TensorProduct

/-- **Explicit finite-Galois tensor decomposition.** For every finite Galois extension `L/k`
of fields in a common universe `u`, there is an `L`-algebra equivalence
`e : L ⊗[k] L ≃ₐ[L] (Gal(L/k) → L)` with `e (a ⊗ₜ b) σ = a * σ b`. The source carries
Mathlib's default `L`-algebra structure through the first tensor factor
(`Algebra.TensorProduct.leftAlgebra`); the target carries the pointwise operations and the
constant structure map (`Pi.algebra`). Thus `a ⊗ₜ 1` goes to the constant function `a` and
`1 ⊗ₜ b` to `σ ↦ σ b`. -/
def FiniteGaloisTensorDecompositionStatement : Prop :=
  ∀ (k L : Type u) [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L],
    ∃ e : (L ⊗[k] L) ≃ₐ[L] (Gal(L/k) → L),
      ∀ (a b : L) (σ : Gal(L/k)), e (a ⊗ₜ[k] b) σ = a * σ b

end Langlands.FieldTheory
