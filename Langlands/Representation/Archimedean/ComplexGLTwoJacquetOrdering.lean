import Langlands.Representation.Archimedean.ComplexJacquetReduction

/-!
# Ordering the Jacquet exponents of `(𝔤𝔩_2(ℂ), U(2))`-modules

This file states `ComplexGLTwoJacquetOrderingStatement`: a `(𝔤𝔩_2(ℂ), U(2))`-module with a
nonzero Jacquet functional has a nonzero Jacquet functional whose exponents `a'` keep the sum
`a'_0 + a'_1` and are ordered, `Re a'_0 ≤ Re a'_1 + 2`. No irreducibility, admissibility or
finite generation is assumed. With `a_j = 2 t_j + 1 - 2 j` the ordering reads
`Re t'_0 ≤ Re t'_1`.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

universe uV

/-- Ordering of Jacquet exponents for `(𝔤𝔩_2(ℂ), U(2))`-modules. Let `(ρ, π)` be a
`(𝔤𝔩_2(ℂ), U(2))`-module (no irreducibility, admissibility or finite generation) and `ℓ` a
nonzero Jacquet functional with exponents `a`, `b`. Then there is a nonzero Jacquet functional
`ℓ'` with exponents `a'`, `b'` such that `a'_0 + a'_1 = a_0 + a_1` and
`Re a'_0 ≤ Re a'_1 + 2`. -/
def ComplexGLTwoJacquetOrderingStatement : Prop :=
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin 2) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsComplexGKModule 2 ρ π →
      ∀ (ℓ : V →ₗ[ℂ] ℂ) (a b : Fin 2 → ℂ), ℓ ≠ 0 → IsComplexJacquetFunctional 2 π ℓ a b →
        ∃ (ℓ' : V →ₗ[ℂ] ℂ) (a' b' : Fin 2 → ℂ), ℓ' ≠ 0 ∧
          IsComplexJacquetFunctional 2 π ℓ' a' b' ∧ a' 0 + a' 1 = a 0 + a 1 ∧
          (a' 0).re ≤ (a' 1).re + 2

end Langlands.Archimedean
