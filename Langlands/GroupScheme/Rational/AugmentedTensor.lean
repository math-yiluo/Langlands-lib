import Mathlib.RingTheory.TensorProduct.Maps

/-! # The two identity slices of an augmented tensor product -/

noncomputable section

universe u v w t

open scoped TensorProduct

namespace Langlands.GroupScheme.RelativeRoot.AugmentedTensor

variable {k : Type u} [CommRing k]
  {A : Type v} [CommRing A] [Algebra k A]
  {B : Type w} [CommRing B] [Algebra k B]

/-- Evaluation at the augmentation in the first tensor factor. -/
def leftIdentitySlice (εA : A →ₐ[k] k) (B : Type w)
    [CommRing B] [Algebra k B] : A ⊗[k] B →ₐ[k] B :=
  (Algebra.TensorProduct.lid k B).toAlgHom.comp
    (Algebra.TensorProduct.map εA (AlgHom.id k B))

/-- Evaluation at the augmentation in the second tensor factor. -/
def rightIdentitySlice (A : Type v) [CommRing A] [Algebra k A]
    (εB : B →ₐ[k] k) : A ⊗[k] B →ₐ[k] A :=
  (Algebra.TensorProduct.rid k k A).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id k A) εB)

@[simp] theorem leftIdentitySlice_tmul (εA : A →ₐ[k] k) (a : A) (b : B) :
    leftIdentitySlice εA B (a ⊗ₜ[k] b) = εA a • b := rfl

@[simp] theorem rightIdentitySlice_tmul (εB : B →ₐ[k] k) (a : A) (b : B) :
    rightIdentitySlice A εB (a ⊗ₜ[k] b) = εB b • a := rfl

/-- Subtracting the scalar part of an element of an augmented algebra. -/
def augmentationPart (εA : A →ₐ[k] k) : A →ₗ[k] A :=
  LinearMap.id - (Algebra.linearMap k A).comp εA.toLinearMap

@[simp] theorem augmentationPart_apply (εA : A →ₐ[k] k) (a : A) :
    augmentationPart εA a = a - algebraMap k A (εA a) := rfl

/-- The scalar-subtraction map with codomain the actual augmentation kernel. -/
def augmentationKernelProjection (εA : A →ₐ[k] k) :
    A →ₗ[k] LinearMap.ker εA.toLinearMap :=
  (augmentationPart εA).codRestrict _ (by
    intro a
    simp)

@[simp] theorem augmentationKernelProjection_coe (εA : A →ₐ[k] k) (a : A) :
    (augmentationKernelProjection εA a : A) = augmentationPart εA a := rfl

theorem map_augmentationPart_left (εA : A →ₐ[k] k) (z : A ⊗[k] B) :
    TensorProduct.map (augmentationPart εA) (LinearMap.id : B →ₗ[k] B) z =
      z - (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B)
        (leftIdentitySlice εA B z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
      simp [TensorProduct.sub_tmul, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul']
  | add x y hx hy =>
      simp only [map_add, hx, hy]
      abel

theorem map_augmentationPart_right (εB : B →ₐ[k] k) (z : A ⊗[k] B) :
    TensorProduct.map (LinearMap.id : A →ₗ[k] A) (augmentationPart εB) z =
      z - (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B)
        (rightIdentitySlice A εB z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
      simp [TensorProduct.tmul_sub, Algebra.algebraMap_eq_smul_one,
        TensorProduct.tmul_smul]
  | add x y hx hy =>
      simp only [map_add, hx, hy]
      abel

/-- Simultaneous vanishing on both identity slices is exactly the tensor of
the two augmentation kernels, viewed inside the actual tensor product. -/
theorem ker_leftIdentitySlice_inf_ker_rightIdentitySlice
    (εA : A →ₐ[k] k) (εB : B →ₐ[k] k) :
    LinearMap.ker (leftIdentitySlice εA B).toLinearMap ⊓
        LinearMap.ker (rightIdentitySlice A εB).toLinearMap =
      LinearMap.range (TensorProduct.mapIncl
        (LinearMap.ker εA.toLinearMap) (LinearMap.ker εB.toLinearMap)) := by
  apply le_antisymm
  · intro z hz
    have hleft : leftIdentitySlice εA B z = 0 := hz.1
    have hright : rightIdentitySlice A εB z = 0 := hz.2
    refine ⟨TensorProduct.map (augmentationKernelProjection εA)
      (augmentationKernelProjection εB) z, ?_⟩
    rw [TensorProduct.mapIncl, TensorProduct.map_map]
    change TensorProduct.map (augmentationPart εA) (augmentationPart εB) z = z
    have hcomp :
        TensorProduct.map (augmentationPart εA) (augmentationPart εB) =
          (TensorProduct.map (augmentationPart εA) (LinearMap.id : B →ₗ[k] B)).comp
            (TensorProduct.map (LinearMap.id : A →ₗ[k] A) (augmentationPart εB)) := by
      rw [← TensorProduct.map_comp]
      simp
    rw [hcomp, LinearMap.comp_apply, map_augmentationPart_right, hright, map_zero,
      sub_zero, map_augmentationPart_left, hleft, map_zero, sub_zero]
  · rintro z ⟨q, rfl⟩
    induction q using TensorProduct.inductionOn with
    | tmul a b =>
        change leftIdentitySlice εA B ((a : A) ⊗ₜ[k] (b : B)) = 0 ∧
          rightIdentitySlice A εB ((a : A) ⊗ₜ[k] (b : B)) = 0
        simp [show εA a = 0 from a.property, show εB b = 0 from b.property]
    | add x y hx hy => simpa only [map_add] using add_mem hx hy

variable {C : Type t} [CommRing C] [Algebra k C]

/-- A coordinate pullback which is constant at the origin on both slices
sends the augmentation kernel into the tensor of the two source kernels. -/
theorem map_augmentationKernel_mem_tensor
    (εA : A →ₐ[k] k) (εB : B →ₐ[k] k) (εC : C →ₐ[k] k)
    (φ : C →ₐ[k] A ⊗[k] B)
    (hleft : (leftIdentitySlice εA B).comp φ = (Algebra.ofId k B).comp εC)
    (hright : (rightIdentitySlice A εB).comp φ = (Algebra.ofId k A).comp εC)
    {c : C} (hc : εC c = 0) :
    φ c ∈ LinearMap.range (TensorProduct.mapIncl
      (LinearMap.ker εA.toLinearMap) (LinearMap.ker εB.toLinearMap)) := by
  rw [← ker_leftIdentitySlice_inf_ker_rightIdentitySlice]
  constructor
  · change leftIdentitySlice εA B (φ c) = 0
    have h := DFunLike.congr_fun hleft c
    simpa [hc] using h
  · change rightIdentitySlice A εB (φ c) = 0
    have h := DFunLike.congr_fun hright c
    simpa [hc] using h

end Langlands.GroupScheme.RelativeRoot.AugmentedTensor
