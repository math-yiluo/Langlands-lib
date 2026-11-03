import Langlands.GroupScheme.Rational.AugmentedTensor
import Langlands.GroupScheme.Rational.AffineCommutatorCoordinates

/-! # The actual commutator pullback on augmentation kernels -/

noncomputable section

universe u v w

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.RelativeRoot.AugmentedTensor

variable {k : Type u} [CommRing k]
  {A : Type v} [CommRing A] [Algebra k A]
  {B : Type w} [CommRing B] [Algebra k B]

/-- The standard first identity slice is the corresponding tensor algebra lift. -/
theorem leftIdentitySlice_eq_lift (εA : A →ₐ[k] k) :
    leftIdentitySlice εA B =
      Algebra.TensorProduct.lift ((Algebra.ofId k B).comp εA) (AlgHom.id k B)
        (fun _ _ => Commute.all _ _) := by
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.ext'
  intro a b
  simp [Algebra.smul_def]

/-- The standard second identity slice is the symmetric tensor algebra lift. -/
theorem rightIdentitySlice_eq_lift (εB : B →ₐ[k] k) :
    rightIdentitySlice A εB =
      Algebra.TensorProduct.lift (AlgHom.id k A) ((Algebra.ofId k A).comp εB)
        (fun _ _ => Commute.all _ _) := by
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.ext'
  intro a b
  simp [Algebra.smul_def, mul_comm]

/-- The two kernel projections give a canonical preimage for every tensor
which vanishes under both identity slices. -/
theorem mapIncl_augmentationKernelProjection_eq
    (εA : A →ₐ[k] k) (εB : B →ₐ[k] k) (z : A ⊗[k] B)
    (hleft : leftIdentitySlice εA B z = 0)
    (hright : rightIdentitySlice A εB z = 0) :
    TensorProduct.mapIncl (LinearMap.ker εA.toLinearMap) (LinearMap.ker εB.toLinearMap)
        (TensorProduct.map (augmentationKernelProjection εA)
          (augmentationKernelProjection εB) z) = z := by
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

end Langlands.GroupScheme.RelativeRoot.AugmentedTensor

namespace Langlands.GroupScheme.RelativeRoot.CommutatorCoordinates

open Lie AugmentedTensor

variable {R : CommRingCat.{u}} {G H K : GroupScheme (Spec R)}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsAffineHom K.X.hom]

/-- The actual commutator's first slice, expressed by the standard identity-slice map. -/
theorem pullback_leftIdentitySlice (i : H ⟶ G) (j : K ⟶ G) :
    (leftIdentitySlice (coordinateOrigin H) (coordinateAlgebra K)).comp (pullback i j) =
      (Algebra.ofId R (coordinateAlgebra K)).comp (coordinateOrigin G) := by
  rw [leftIdentitySlice_eq_lift]
  exact pullback_left_identity_slice i j

/-- The actual commutator's second slice, expressed by the standard identity-slice map. -/
theorem pullback_rightIdentitySlice (i : H ⟶ G) (j : K ⟶ G) :
    (rightIdentitySlice (coordinateAlgebra H) (coordinateOrigin K)).comp (pullback i j) =
      (Algebra.ofId R (coordinateAlgebra H)).comp (coordinateOrigin G) := by
  rw [rightIdentitySlice_eq_lift]
  exact pullback_right_identity_slice i j

/-- The actual commutator pullback on augmentation kernels, canonically
factored into the tensor product of the two source augmentation kernels. -/
def augmentationPullback (i : H ⟶ G) (j : K ⟶ G) :
    LinearMap.ker (coordinateOrigin G).toLinearMap →ₗ[R]
      (LinearMap.ker (coordinateOrigin H).toLinearMap) ⊗[R]
        (LinearMap.ker (coordinateOrigin K).toLinearMap) :=
  (TensorProduct.map (augmentationKernelProjection (coordinateOrigin H))
      (augmentationKernelProjection (coordinateOrigin K))).comp
    ((pullback i j).toLinearMap.domRestrict (LinearMap.ker (coordinateOrigin G).toLinearMap))

/-- Including the kernel tensor recovers the actual commutator coordinate pullback. -/
theorem augmentationPullback_include (i : H ⟶ G) (j : K ⟶ G)
    (c : LinearMap.ker (coordinateOrigin G).toLinearMap) :
    TensorProduct.mapIncl
      (LinearMap.ker (coordinateOrigin H).toLinearMap)
      (LinearMap.ker (coordinateOrigin K).toLinearMap)
      (augmentationPullback i j c) = pullback i j c := by
  apply mapIncl_augmentationKernelProjection_eq
  · have h := DFunLike.congr_fun (pullback_leftIdentitySlice i j) (c : coordinateAlgebra G)
    simpa [show coordinateOrigin G c = 0 from c.property] using h
  · have h := DFunLike.congr_fun (pullback_rightIdentitySlice i j) (c : coordinateAlgebra G)
    simpa [show coordinateOrigin G c = 0 from c.property] using h

/-- Every actual commutator pullback of an augmentation element lies in the
range of the tensor of the two coordinate augmentation-kernel inclusions. -/
theorem pullback_mem_augmentationTensor (i : H ⟶ G) (j : K ⟶ G)
    {c : coordinateAlgebra G} (hc : coordinateOrigin G c = 0) :
    pullback i j c ∈ LinearMap.range (TensorProduct.mapIncl
      (LinearMap.ker (coordinateOrigin H).toLinearMap)
      (LinearMap.ker (coordinateOrigin K).toLinearMap)) :=
  ⟨augmentationPullback i j ⟨c, hc⟩, augmentationPullback_include i j ⟨c, hc⟩⟩

end Langlands.GroupScheme.RelativeRoot.CommutatorCoordinates
