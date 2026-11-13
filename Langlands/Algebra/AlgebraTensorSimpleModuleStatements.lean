import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Basic.Complex.Basic

/-!
# Simple modules over a tensor product of algebras (Renard III.1.14, Scholium)

For unital complex algebras `A₁`, `A₂` and finite-dimensional simple modules `V₁`, `V₂`, the
module `V₁ ⊗ V₂` over `A₁ ⊗ A₂` is simple; every finite-dimensional simple
`A₁ ⊗ A₂`-module is of this form, and the factors are unique up to isomorphism.
-/

open scoped TensorProduct

namespace Langlands

universe u₁ u₂ v v₁ v₂ w₁ w₂

/-- Renard III.1.14, Scholium, first assertion: for unital complex algebras `A₁`, `A₂` and
finite-dimensional simple modules `V₁`, `V₂`, the representation `τ₁ ⊠ τ₂` of `A₁ ⊗ A₂` on
`V₁ ⊗ V₂`, `(a₁ ⊗ a₂)(v₁ ⊗ v₂) = a₁ v₁ ⊗ a₂ v₂`, is irreducible: `V₁ ⊗ V₂` is nonzero and its
only complex subspaces stable under `A₁ ⊗ A₂` are `0` and `V₁ ⊗ V₂`. -/
def AlgebraExternalTensorSimpleStatement : Prop :=
  ∀ (A₁ : Type u₁) (A₂ : Type u₂) [Ring A₁] [Algebra ℂ A₁] [Ring A₂] [Algebra ℂ A₂]
    (V₁ : Type v₁) (V₂ : Type v₂)
    [AddCommGroup V₁] [Module ℂ V₁] [Module A₁ V₁] [IsScalarTower ℂ A₁ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [Module A₂ V₂] [IsScalarTower ℂ A₂ V₂],
    FiniteDimensional ℂ V₁ → IsSimpleModule A₁ V₁ →
    FiniteDimensional ℂ V₂ → IsSimpleModule A₂ V₂ →
    let σ : A₁ ⊗[ℂ] A₂ →ₐ[ℂ] Module.End ℂ (V₁ ⊗[ℂ] V₂) :=
      (Module.endTensorEndAlgHom (R := ℂ) (S := ℂ) (A := ℂ)).comp
        (Algebra.TensorProduct.map (Algebra.lsmul ℂ ℂ V₁) (Algebra.lsmul ℂ ℂ V₂))
    Nontrivial (V₁ ⊗[ℂ] V₂) ∧
      ∀ U : Submodule ℂ (V₁ ⊗[ℂ] V₂), (∀ (a : A₁ ⊗[ℂ] A₂) (x : V₁ ⊗[ℂ] V₂), x ∈ U → σ a x ∈ U) →
        U = ⊥ ∨ U = ⊤

/-- Renard III.1.14, Scholium, second assertion (existence): every finite-dimensional simple
module `W` over `A₁ ⊗ A₂` is isomorphic to `τ₁ ⊠ τ₂` for finite-dimensional simple modules
`V₁` over `A₁` and `V₂` over `A₂`: there is a complex-linear bijection `e : V₁ ⊗ V₂ ≃ W`
with `e((a₁ ⊗ a₂) x) = (a₁ ⊗ a₂) e(x)`. -/
def AlgebraTensorSimpleFactorizationStatement : Prop :=
  ∀ (A₁ : Type u₁) (A₂ : Type u₂) [Ring A₁] [Algebra ℂ A₁] [Ring A₂] [Algebra ℂ A₂]
    (W : Type v) [AddCommGroup W] [Module ℂ W] [Module (A₁ ⊗[ℂ] A₂) W]
    [IsScalarTower ℂ (A₁ ⊗[ℂ] A₂) W],
    FiniteDimensional ℂ W → IsSimpleModule (A₁ ⊗[ℂ] A₂) W →
    ∃ (V₁ : Type v) (_ : AddCommGroup V₁) (_ : Module ℂ V₁) (_ : Module A₁ V₁)
      (_ : IsScalarTower ℂ A₁ V₁)
      (V₂ : Type v) (_ : AddCommGroup V₂) (_ : Module ℂ V₂) (_ : Module A₂ V₂)
      (_ : IsScalarTower ℂ A₂ V₂),
      FiniteDimensional ℂ V₁ ∧ IsSimpleModule A₁ V₁ ∧
      FiniteDimensional ℂ V₂ ∧ IsSimpleModule A₂ V₂ ∧
      let σ : A₁ ⊗[ℂ] A₂ →ₐ[ℂ] Module.End ℂ (V₁ ⊗[ℂ] V₂) :=
        (Module.endTensorEndAlgHom (R := ℂ) (S := ℂ) (A := ℂ)).comp
          (Algebra.TensorProduct.map (Algebra.lsmul ℂ ℂ V₁) (Algebra.lsmul ℂ ℂ V₂))
      ∃ e : V₁ ⊗[ℂ] V₂ ≃ₗ[ℂ] W, ∀ (a : A₁ ⊗[ℂ] A₂) (x : V₁ ⊗[ℂ] V₂), e (σ a x) = a • e x

/-- Renard III.1.14, Scholium, second assertion (uniqueness): if `τ₁ ⊠ τ₂` and `τ₁' ⊠ τ₂'`,
for finite-dimensional simple modules over `A₁` and `A₂`, are isomorphic representations of
`A₁ ⊗ A₂`, then `V₁ ≅ V₁'` as `A₁`-modules and `V₂ ≅ V₂'` as `A₂`-modules. -/
def AlgebraTensorFactorUniquenessStatement : Prop :=
  ∀ (A₁ : Type u₁) (A₂ : Type u₂) [Ring A₁] [Algebra ℂ A₁] [Ring A₂] [Algebra ℂ A₂]
    (V₁ : Type v₁) (V₂ : Type v₂) (W₁ : Type w₁) (W₂ : Type w₂)
    [AddCommGroup V₁] [Module ℂ V₁] [Module A₁ V₁] [IsScalarTower ℂ A₁ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [Module A₂ V₂] [IsScalarTower ℂ A₂ V₂]
    [AddCommGroup W₁] [Module ℂ W₁] [Module A₁ W₁] [IsScalarTower ℂ A₁ W₁]
    [AddCommGroup W₂] [Module ℂ W₂] [Module A₂ W₂] [IsScalarTower ℂ A₂ W₂],
    FiniteDimensional ℂ V₁ → IsSimpleModule A₁ V₁ →
    FiniteDimensional ℂ V₂ → IsSimpleModule A₂ V₂ →
    FiniteDimensional ℂ W₁ → IsSimpleModule A₁ W₁ →
    FiniteDimensional ℂ W₂ → IsSimpleModule A₂ W₂ →
    let σ : A₁ ⊗[ℂ] A₂ →ₐ[ℂ] Module.End ℂ (V₁ ⊗[ℂ] V₂) :=
      (Module.endTensorEndAlgHom (R := ℂ) (S := ℂ) (A := ℂ)).comp
        (Algebra.TensorProduct.map (Algebra.lsmul ℂ ℂ V₁) (Algebra.lsmul ℂ ℂ V₂))
    let σ' : A₁ ⊗[ℂ] A₂ →ₐ[ℂ] Module.End ℂ (W₁ ⊗[ℂ] W₂) :=
      (Module.endTensorEndAlgHom (R := ℂ) (S := ℂ) (A := ℂ)).comp
        (Algebra.TensorProduct.map (Algebra.lsmul ℂ ℂ W₁) (Algebra.lsmul ℂ ℂ W₂))
    ∀ e : V₁ ⊗[ℂ] V₂ ≃ₗ[ℂ] W₁ ⊗[ℂ] W₂,
      (∀ (a : A₁ ⊗[ℂ] A₂) (x : V₁ ⊗[ℂ] V₂), e (σ a x) = σ' a (e x)) →
      Nonempty (V₁ ≃ₗ[A₁] W₁) ∧ Nonempty (V₂ ≃ₗ[A₂] W₂)

/-- Renard III.1.14, Scholium: irreducibility of `τ₁ ⊠ τ₂`, existence of the factorization
of finite-dimensional simple `A₁ ⊗ A₂`-modules, and uniqueness of the factors. -/
def AlgebraTensorScholiumStatement : Prop :=
  AlgebraExternalTensorSimpleStatement.{u₁, u₂, v₁, v₂} ∧
  AlgebraTensorSimpleFactorizationStatement.{u₁, u₂, v} ∧
  AlgebraTensorFactorUniquenessStatement.{u₁, u₂, v₁, v₂, w₁, w₂}

end Langlands
