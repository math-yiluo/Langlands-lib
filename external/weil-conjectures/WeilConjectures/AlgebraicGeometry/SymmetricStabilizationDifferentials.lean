/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Kaehler.Basic
import WeilConjectures.RingTheory.ReducedTensorDifferentials
import WeilConjectures.RingTheory.SymmetricAlgebraDifferentials

/-! # Reduced differentials of symmetric-algebra stabilization

Source: Stacks Project, More on Algebra, Tag 07M7, first paragraph.
-/

@[expose] public section

universe u
open scoped TensorProduct
namespace AlgebraicGeometry

/-- Reduced differentials of a symmetric stabilization split into the original
reduced differentials and the scalar extension of the stabilizing module.

Source: Stacks Project, More on Algebra, Tag 07M7, first paragraph; differentials
of tensor products and the universal property of the symmetric algebra.
(blueprint: lem-weil-pbc-symmetric-stabilization-differentials)

Proof: write S = Sym_A₁(K) and D = S tensor_A B. The universal property of
A₁-derivations on D identifies them with a pair consisting of an A₁-derivation
on S and an A-derivation on B. A derivation on S is uniquely determined by an
A₁-linear map from K, because S is the symmetric algebra. The universal
property of Kahler differentials therefore gives the direct sum of
D tensor_B Omega[B/A] and D tensor_A₁ K. Tensor this identity with Q over D.
Associativity and cancellation of tensor products give Q tensor_B Omega[B/A]
and Q tensor_A₁ K. The two compatibility equations ensure that the B and A₁
scalar actions are exactly those specified by sigma and eta. Finite products
are direct sums of modules. This argument requires neither smoothness nor
nonzero rings and works also for K = 0.
-/
theorem symmetric_stabilization_differentials
    (A B Q : Type u) [CommRing A] [CommRing B] [CommRing Q]
    [Algebra A B] [Algebra A Q] (A₁ : CommAlgCat.{u} A)
    (K : Type u) [AddCommGroup K] [Module A₁ K]
    [Algebra A (SymmetricAlgebra A₁ K)]
    [IsScalarTower A A₁ (SymmetricAlgebra A₁ K)]
    (σ : B →ₐ[A] Q) (η : A₁ →ₐ[A] Q)
    (τ : (SymmetricAlgebra A₁ K ⊗[A] B) →ₐ[A] Q)
    (hσ : τ.comp Algebra.TensorProduct.includeRight = σ)
    (hη : ∀ a : A₁, τ (algebraMap A₁ (SymmetricAlgebra A₁ K ⊗[A] B) a) = η a) :
    letI : Algebra B Q := σ.toRingHom.toAlgebra
    letI : Algebra A₁ Q := η.toRingHom.toAlgebra
    letI : Algebra (SymmetricAlgebra A₁ K ⊗[A] B) Q := τ.toRingHom.toAlgebra
    Nonempty ((Q ⊗[SymmetricAlgebra A₁ K ⊗[A] B]
      KaehlerDifferential A₁ (SymmetricAlgebra A₁ K ⊗[A] B)) ≃ₗ[Q]
        ((Q ⊗[B] KaehlerDifferential A B) × (Q ⊗[A₁] K))) := by
  let S := SymmetricAlgebra A₁ K
  let : Algebra B Q := σ.toRingHom.toAlgebra
  let : Algebra A₁ Q := η.toRingHom.toAlgebra
  let : Algebra S Q :=
    (τ.comp Algebra.TensorProduct.includeLeft).toRingHom.toAlgebra
  let : Algebra (S ⊗[A] B) Q := τ.toRingHom.toAlgebra
  have : IsScalarTower A₁ S Q := IsScalarTower.of_algebraMap_eq fun a => by
    change η a = τ (algebraMap A₁ S a ⊗ₜ[A] (1 : B))
    exact (hη a).symm
  obtain ⟨eTensor⟩ := reduced_tensor_differentials A A₁ S B Q σ η τ hσ hη
  obtain ⟨eSym, _⟩ := symmetric_algebra_differentials A₁ K
  let eBase := LinearEquiv.baseChange S Q _ _ eSym
  let eCancel := TensorProduct.AlgebraTensorModule.cancelBaseChange A₁ S Q Q K
  exact ⟨eTensor.trans
    ((LinearEquiv.refl Q _).prodCongr (eBase.trans eCancel))⟩

end AlgebraicGeometry
