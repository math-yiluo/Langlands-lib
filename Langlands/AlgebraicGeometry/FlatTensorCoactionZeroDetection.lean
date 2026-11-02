import Mathlib.RingTheory.Flat.Basic

/-! # Zero detection for a flat tensor coaction -/

universe u v w

open TensorProduct

namespace Langlands.AlgebraicGeometry

variable {A : Type u} {B : Type v} {M : Type w}
  [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M]

/-- The unit map used in the fixed-element equation for a tensor coaction. -/
def tensorCoactionUnit : M →ₗ[A] B ⊗[A] M :=
  TensorProduct.mk A B M (1 : B)

@[simp]
lemma tensorCoactionUnit_apply (m : M) :
    tensorCoactionUnit (A := A) (B := B) m = (1 : B) ⊗ₜ[A] m :=
  rfl

variable [Module.Flat A B]

/-- If the only fixed element of an injective flat tensor coaction is zero,
the underlying module is zero. -/
lemma subsingleton_of_flat_tensor_coaction
    (δ : M →ₗ[A] B ⊗[A] M) (hδ : Function.Injective δ)
    (hcoassoc : ∀ m : M,
      LinearMap.lTensor B δ (δ m) =
        LinearMap.lTensor B tensorCoactionUnit (δ m))
    (hfixed : ∀ m : M, δ m = (1 : B) ⊗ₜ[A] m → m = 0) :
    Subsingleton M := by
  let η : M →ₗ[A] B ⊗[A] M := tensorCoactionUnit
  have hd : Function.Injective (δ - η) := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hfixed
    have hz : (δ - η) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp hz
  have htd := Module.Flat.lTensor_preserves_injective_linearMap (M := B) (δ - η) hd
  have hz (m : M) : δ m = 0 := by
    apply htd
    simpa only [LinearMap.lTensor_sub, LinearMap.sub_apply, map_zero,
      sub_eq_zero] using hcoassoc m
  exact ⟨fun x y => hδ ((hz x).trans (hz y).symm)⟩

/-- A nonzero module with an injective flat tensor coaction has a nonzero
fixed element. -/
lemma exists_nonzero_fixed_of_flat_tensor_coaction [Nontrivial M]
    (δ : M →ₗ[A] B ⊗[A] M) (hδ : Function.Injective δ)
    (hcoassoc : ∀ m : M,
      LinearMap.lTensor B δ (δ m) =
        LinearMap.lTensor B tensorCoactionUnit (δ m)) :
    ∃ m : M, δ m = (1 : B) ⊗ₜ[A] m ∧ m ≠ 0 := by
  by_contra! h
  have : Subsingleton M := subsingleton_of_flat_tensor_coaction δ hδ hcoassoc h
  exact not_subsingleton M inferInstance

end Langlands.AlgebraicGeometry
