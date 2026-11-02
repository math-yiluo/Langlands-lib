import Langlands.AlgebraicGeometry.GroupoidCoactionUniversal
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Tensor presentations of groupoid coactions -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable {M : Type v} [AddCommGroup M] [Module B M] [Module A M]
  [IsScalarTower A B M]

/-- The module coordinate change associated to a tensor presentation of the
relation ring. -/
noncomputable def presentationTensorEquiv (e : C ≃ₐ[B] B ⊗[A] B) :
    C ⊗[B] M ≃ₗ[A] B ⊗[A] M :=
  (((TensorProduct.comm B C M).trans
    (TensorProduct.congr (LinearEquiv.refl B M) e.toLinearEquiv)).restrictScalars A).trans
    (((AlgebraTensorModule.cancelBaseChange A B B M B).restrictScalars A).trans
      (TensorProduct.comm A M B))

@[simp]
lemma presentationTensorEquiv_tmul (e : C ≃ₐ[B] B ⊗[A] B) (b₁ b₂ : B) (m : M) :
    presentationTensorEquiv (M := M) e
      (e.symm (b₁ ⊗ₜ[A] b₂) ⊗ₜ[B] m) = b₂ ⊗ₜ[A] (b₁ • m) := by
  simp [presentationTensorEquiv]

@[simp]
lemma presentationTensorEquiv_one_tmul (e : C ≃ₐ[B] B ⊗[A] B) (m : M) :
    presentationTensorEquiv (M := M) e ((1 : C) ⊗ₜ[B] m) =
      (1 : B) ⊗ₜ[A] m := by
  have h := presentationTensorEquiv_tmul e (1 : B) 1 m
  change presentationTensorEquiv e (e.symm (1 : B ⊗[A] B) ⊗ₜ[B] m) =
    (1 : B) ⊗ₜ[A] ((1 : B) • m) at h
  simpa using h

variable {t : B →+* C}

/-- Tensor-presentation coordinates identify source and target on the base ring. -/
lemma target_comp_algebraMap_of_presentation
    (e : C ≃ₐ[B] B ⊗[A] B)
    (ht : ∀ b : B, e (t b) = (1 : B) ⊗ₜ[A] b) :
    t.comp (algebraMap A B) = algebraMap A C := by
  ext a
  apply e.injective
  rw [RingHom.comp_apply, ht, IsScalarTower.algebraMap_apply A B C,
    e.commutes]
  change (1 : B) ⊗ₜ[A] (algebraMap A B a) =
    (algebraMap A B a) ⊗ₜ[A] (1 : B)
  simpa only [Algebra.smul_def, mul_one] using
    (TensorProduct.smul_tmul a (1 : B) (1 : B)).symm

/-- The published additive coaction is linear over the presentation base. -/
def presentationCoactionLinear (θ : GroupoidCoaction t M)
    (e : C ≃ₐ[B] B ⊗[A] B)
    (ht : ∀ b : B, e (t b) = (1 : B) ⊗ₜ[A] b) :
    M →ₗ[A] C ⊗[B] M where
  toAddHom := θ.coaction
  map_smul' a m := by
    change θ.coaction (a • m) = a • θ.coaction m
    rw [← IsScalarTower.algebraMap_smul B a m, θ.map_smul]
    have ha := congrArg (fun f : A →+* C => f a)
      (target_comp_algebraMap_of_presentation e ht)
    rw [RingHom.comp_apply] at ha
    rw [ha, IsScalarTower.algebraMap_smul]

/-- The coaction in ordinary tensor coordinates. -/
noncomputable def presentationCoaction (θ : GroupoidCoaction t M)
    (e : C ≃ₐ[B] B ⊗[A] B)
    (ht : ∀ b : B, e (t b) = (1 : B) ⊗ₜ[A] b) :
    M →ₗ[A] B ⊗[A] M :=
  (presentationTensorEquiv e).toLinearMap.comp (presentationCoactionLinear θ e ht)

lemma presentationCoaction_fixed_iff (θ : GroupoidCoaction t M)
    (e : C ≃ₐ[B] B ⊗[A] B)
    (ht : ∀ b : B, e (t b) = (1 : B) ⊗ₜ[A] b) (m : M) :
    presentationCoaction θ e ht m = (1 : B) ⊗ₜ[A] m ↔
      m ∈ θ.invariants := by
  change presentationTensorEquiv e (θ.coaction m) = (1 : B) ⊗ₜ[A] m ↔
    θ.coaction m = (1 : C) ⊗ₜ[B] m
  rw [← presentationTensorEquiv_one_tmul e]
  exact (presentationTensorEquiv e).injective.eq_iff

lemma coaction_injective_of_ringRelation (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M) : Function.Injective θ.coaction := by
  intro x y h
  have h' := congrArg (LinearMap.rTensor M hE.identity.toLinearMap) h
  rw [θ.counit B hE.identity hE.identity_comp_t,
    θ.counit B hE.identity hE.identity_comp_t] at h'
  simpa using congrArg (TensorProduct.lid B M) h'

lemma presentationCoaction_injective (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M) (e : C ≃ₐ[B] B ⊗[A] B)
    (ht : ∀ b : B, e (t b) = (1 : B) ⊗ₜ[A] b) :
    Function.Injective (presentationCoaction θ e ht) :=
  (presentationTensorEquiv e).injective.comp (coaction_injective_of_ringRelation hE θ)

end Langlands.AlgebraicGeometry.GroupoidCoaction
