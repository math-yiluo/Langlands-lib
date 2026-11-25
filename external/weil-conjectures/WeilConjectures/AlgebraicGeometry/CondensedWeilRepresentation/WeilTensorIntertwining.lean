/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RepresentationTheory.Basic
import WeilConjectures.AlgebraicGeometry.CondensedWeilRepresentation.WeilActionIntertwining

/-! # Extending tensor equivariance from geometric monodromy and Frobenius

Source: latest blueprint, prop-wf-weil-sheaf-representation-equivalence.proof.md,
Frobenius descent and the final tensor paragraph.
(blueprint: lem-wrp-weil-tensor-intertwining).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w z r
open scoped TensorProduct

namespace AlgebraicGeometry.ProEtale.CondensedWeilRepresentation

/-- Equivariance of a linear tensor map can be checked on geometric elements and the
chosen degree-one lift, and only on pure tensors at those elements.

Source: prop-wf-weil-sheaf-representation-equivalence.proof.md, Frobenius descent's
morphism criterion and the tensor comparison in the exactness paragraph.
(blueprint: lem-wrp-weil-tensor-intertwining).

Proof: pure tensors span the tensor product, so each stipulated pure-tensor identity
is the equality of the two linear maps on the whole tensor product. The diagonal
tensor representation and the target representation give actions of W on the two
modules. Apply the geometric-subgroup and degree-one equivariance criterion to the
underlying function of b, then specialize the resulting identity to a pure tensor. -/
theorem tensor_equivariant_of_kernel_and_degreeOne
    {W : Type u} [Group W] (deg : W →* Multiplicative ℤ)
    (γ : W) (hγ : deg γ = Multiplicative.ofAdd 1)
    {R : Type r} [CommSemiring R]
    {V : Type v} [AddCommMonoid V] [Module R V]
    {U : Type w} [AddCommMonoid U] [Module R U]
    {T : Type z} [AddCommMonoid T] [Module R T]
    (ρV : Representation R W V) (ρU : Representation R W U)
    (ρT : Representation R W T) (b : V ⊗[R] U →ₗ[R] T)
    (hker : ∀ (g : deg.ker) (v : V) (w : U),
      b (ρV g v ⊗ₜ ρU g w) = ρT g (b (v ⊗ₜ w)))
    (hfrob : ∀ (v : V) (w : U),
      b (ρV γ v ⊗ₜ ρU γ w) = ρT γ (b (v ⊗ₜ w))) :
    ∀ (g : W) (v : V) (w : U), b (ρV g v ⊗ₜ ρU g w) = ρT g (b (v ⊗ₜ w)) := by
  let ρ := ρV.tprod ρU
  let : MulAction W (V ⊗[R] U) :=
    { smul := fun g v ↦ ρ g v
      one_smul := fun v ↦ congrArg (fun f ↦ f v) ρ.map_one
      mul_smul := fun g h v ↦ congrArg (fun f ↦ f v) (ρ.map_mul g h) }
  let : MulAction W T :=
    { smul := fun g v ↦ ρT g v
      one_smul := fun v ↦ congrArg (fun f ↦ f v) ρT.map_one
      mul_smul := fun g h v ↦ congrArg (fun f ↦ f v) (ρT.map_mul g h) }
  have hk (g : deg.ker) (v : V ⊗[R] U) : b ((g : W) • v) = (g : W) • b v := by
    have he : b.comp (ρ g) = (ρT g).comp b := by
      ext v w
      exact hker g v w
    exact congrArg (fun f : V ⊗[R] U →ₗ[R] T ↦ f v) he
  have hf (v : V ⊗[R] U) : b (γ • v) = γ • b v := by
    have he : b.comp (ρ γ) = (ρT γ).comp b := by
      ext v w
      exact hfrob v w
    exact congrArg (fun f : V ⊗[R] U →ₗ[R] T ↦ f v) he
  have hall := (equivariant_iff_kernel_and_degreeOne deg γ hγ b).mpr ⟨hk, hf⟩
  intro g v w
  exact hall g (v ⊗ₜ w)

end AlgebraicGeometry.ProEtale.CondensedWeilRepresentation
