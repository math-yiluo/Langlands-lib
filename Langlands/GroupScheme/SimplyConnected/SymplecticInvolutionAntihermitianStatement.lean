import Langlands.GroupScheme.Quaternionic.Forms
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.RingTheory.SimpleRing.Defs
import Mathlib.Algebra.Central.Defs

/-! # Symplectic involutions are adjoint to antihermitian division forms: statement -/

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme

/-- Let `A` be a finite-dimensional central simple `K`-algebra with an involution of the first
kind `τ`. Suppose that some field extension `L/K` and an `L`-algebra isomorphism
`e : L ⊗[K] A ≃ M_{2n}(L)` carry `τ_L` to the adjoint involution of the standard alternating
matrix `J`, in the form `e (τ_L x) * J = J * ᵗ(e x)`. Then there are a central division
`K`-algebra `D` of degree `degree`, with `m * degree = 2 * n`, an involution of the first kind
`σ` of `D` whose symmetric space has dimension `degree * (degree + 1) / 2`, an invertible
trace-valued `σ`-antihermitian Gram matrix `H ∈ M_m(D)` and a `K`-algebra isomorphism
`φ : A ≃ M_m(D)` with `φ (τ x) * H = H * ᵗ(φ x)^σ` for every `x`; that is, `φ` carries `τ` to
the adjoint involution `y ↦ H ᵗy^σ H⁻¹` of `H`. -/
def SymplecticInvolutionAntihermitianStatement : Prop :=
  ∀ (K A : Type u) [Field K] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] (τ : Quaternionic.FirstKindInvolution K A) (n : ℕ)
    (L : Type u) [Field L] [Algebra K L]
    (e : L ⊗[K] A ≃ₐ[L] Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L),
    (∀ x, e (τ.baseChange L x) * Matrix.J (Fin n) L = Matrix.J (Fin n) L * (e x).transpose) →
      ∃ (degree m : ℕ) (_ : NeZero m)
        (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
        (_ : Algebra.IsCentral K D) (_ : FiniteDimensional K D),
        0 < degree ∧ m * degree = 2 * n ∧
        Module.finrank K D = degree ^ 2 ∧
          ∃ σ : Quaternionic.FirstKindInvolution K D,
            Module.finrank K σ.symmetricSubspace = degree * (degree + 1) / 2 ∧
              ∃ H : Matrix (Fin m) (Fin m) D,
                σ.IsAntihermitian H ∧ IsUnit H ∧
                  ∃ φ : A ≃ₐ[K] Matrix (Fin m) (Fin m) D,
                    ∀ x, φ (τ x) * H = H * σ.matrix (Fin m) (φ x)

end Langlands.GroupScheme
