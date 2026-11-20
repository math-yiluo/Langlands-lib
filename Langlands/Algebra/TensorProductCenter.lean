import Langlands.Algebra.TensorProductCenterMap
import Langlands.Algebra.EnvelopingLieProduct
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic

/-! # The center of a tensor product of algebras over a field -/

noncomputable section
universe u v w

open scoped TensorProduct

set_option autoImplicit false

namespace Langlands.Algebra

variable (K : Type u) [Field K] (A : Type v) [Ring A] [Algebra K A]
  (B : Type w) [Ring B] [Algebra K B]

local notation "ZA" => Subalgebra.center K A
local notation "ZB" => Subalgebra.center K B

private def leftCenterInclusion : ZA ⊗[K] B →ₐ[K] A ⊗[K] B :=
  Algebra.TensorProduct.map (ZA).val (AlgHom.id K B)

private def rightCenterInclusion : ZA ⊗[K] ZB →ₐ[K] ZA ⊗[K] B :=
  Algebra.TensorProduct.map (AlgHom.id K ZA) (ZB).val

private theorem leftCenterInclusion_injective : Function.Injective (leftCenterInclusion K A B) := by
  have h : (leftCenterInclusion K A B).toLinearMap = (ZA).val.toLinearMap.rTensor B :=
    TensorProduct.ext' fun _ _ => rfl
  change Function.Injective (leftCenterInclusion K A B).toLinearMap
  rw [h]
  exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective

private theorem rightCenterInclusion_injective : Function.Injective (rightCenterInclusion K A B) := by
  have h : (rightCenterInclusion K A B).toLinearMap = (ZB).val.toLinearMap.lTensor ZA :=
    TensorProduct.ext' fun _ _ => rfl
  change Function.Injective (rightCenterInclusion K A B).toLinearMap
  rw [h]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective

private theorem tensorCenterMap_mem_center (z : ZA ⊗[K] ZB) :
    ((leftCenterInclusion K A B).comp (rightCenterInclusion K A B)) z ∈
      Subalgebra.center K (A ⊗[K] B) := by
  apply Subalgebra.mem_center_iff.mpr
  intro a
  induction a using TensorProduct.inductionOn with
  | tmul a b =>
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      change (a ⊗ₜ[K] b) * (x.val ⊗ₜ[K] y.val) = (x.val ⊗ₜ[K] y.val) * (a ⊗ₜ[K] b)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        Subalgebra.mem_center_iff.mp x.property a, Subalgebra.mem_center_iff.mp y.property b]
    | add x y hx hy => simp only [map_add, mul_add, add_mul, hx, hy]
  | add a b ha hb => simp only [add_mul, mul_add, ha, hb]

private def tensorCenterMap : ZA ⊗[K] ZB →ₐ[K] Subalgebra.center K (A ⊗[K] B) :=
  ((leftCenterInclusion K A B).comp (rightCenterInclusion K A B)).codRestrict _
    (tensorCenterMap_mem_center K A B)

private theorem tensorCenterMap_bijective : Function.Bijective (tensorCenterMap K A B) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply rightCenterInclusion_injective K A B
    apply leftCenterInclusion_injective K A B
    exact congrArg Subtype.val hxy
  · intro z
    have hzL : z.val ∈ Subalgebra.centralizer K
        (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B).range :=
      Subalgebra.center_le_centralizer K _ z.property
    rw [Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct] at hzL
    obtain ⟨x, hx⟩ := hzL
    change leftCenterInclusion K A B x = z.val at hx
    have hzR : x ∈ Subalgebra.centralizer K
        (Algebra.TensorProduct.includeRight : B →ₐ[K] ZA ⊗[K] B).range := by
      apply (Subalgebra.mem_centralizer_iff K).mpr
      rintro _ ⟨b, rfl⟩
      apply leftCenterInclusion_injective K A B
      rw [map_mul, map_mul, hx]
      have hright : leftCenterInclusion K A B
          ((Algebra.TensorProduct.includeRight : B →ₐ[K] ZA ⊗[K] B) b) =
            (Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B) b := by
        simp only [leftCenterInclusion, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
      change leftCenterInclusion K A B
          ((Algebra.TensorProduct.includeRight : B →ₐ[K] ZA ⊗[K] B) b) * z.val =
        z.val * leftCenterInclusion K A B
          ((Algebra.TensorProduct.includeRight : B →ₐ[K] ZA ⊗[K] B) b)
      rw [hright]
      exact Subalgebra.mem_center_iff.mp z.property _
    rw [Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct] at hzR
    obtain ⟨w, hw⟩ := hzR
    refine ⟨w, Subtype.ext ?_⟩
    change leftCenterInclusion K A B (rightCenterInclusion K A B w) = z.val
    rw [show rightCenterInclusion K A B w = x from hw, hx]

/-- Over a field, the tensor product of the two centers is exactly the center
of the tensor product. -/
def tensorProductCenter :
    (ZA ⊗[K] ZB) ≃ₐ[K] Subalgebra.center K (A ⊗[K] B) :=
  AlgEquiv.ofBijective (tensorCenterMap K A B) (tensorCenterMap_bijective K A B)

@[simp]
theorem tensorProductCenter_tmul (x : ZA) (y : ZB) :
    (tensorProductCenter K A B (x ⊗ₜ[K] y)).val = x.val ⊗ₜ[K] y.val :=
  rfl

namespace LieEnvelopingEquiv

variable (L : Type v) (M : Type w)
  [LieRing L] [LieAlgebra K L] [LieRing M] [LieAlgebra K M]

/-- The center of the enveloping algebra of a product Lie algebra is the
tensor product of the two enveloping centers. -/
def envelopingProductCenter :
    Subalgebra.center K (UniversalEnvelopingAlgebra K (L × M)) ≃ₐ[K]
      (Subalgebra.center K (UniversalEnvelopingAlgebra K L) ⊗[K]
        Subalgebra.center K (UniversalEnvelopingAlgebra K M)) :=
  (center (envelopingProduct K L M)).trans
    (tensorProductCenter K (UniversalEnvelopingAlgebra K L) (UniversalEnvelopingAlgebra K M)).symm

end LieEnvelopingEquiv

end Langlands.Algebra
