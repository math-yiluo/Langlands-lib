import Langlands.GroupScheme.Rational.AffineCommutatorImageAction
import Langlands.GroupScheme.Rational.AffineCommutatorImageCoordinates
import Langlands.GroupScheme.Rational.PointedTensorWeights
import Langlands.GroupScheme.Rational.AffineCommutatorAugmentation

/-! # Actual pointed commutator image pullback and augmentation tensors -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.PointedCoordinateWeights

open RelativeRoot.AugmentedTensor

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {V W : Over (Spec (CommRingCat.of k))}
    [IsAffineHom V.hom] [IsAffineHom W.hom]

/-- Pullback along a constant rational point is evaluation at that point. -/
theorem pullback_constant_origin (a : PointedAction S V) :
    pullback (toUnit W ≫ a.origin) =
      (Algebra.ofId k (Coord W)).comp (coordinateOrigin a) := by
  rw [pullback, comp_toUnit_assoc, pointCoordinates_origin]

/-- The first coordinate identity slice is the pullback of the actual first
pointed slice under the actual tensor presentation. -/
theorem tensorCoordinates_leftIdentitySlice (a : PointedAction S V) :
    (leftIdentitySlice (coordinateOrigin a) (Coord W)).comp
        (tensorCoordinates (V := V) (W := W)).toAlgHom =
      pullback (lift (toUnit W ≫ a.origin) (𝟙 W)) := by
  have h :
      (pullback (lift (toUnit W ≫ a.origin) (𝟙 W))).comp
          (tensorCoordinates (V := V) (W := W)).symm.toAlgHom =
        leftIdentitySlice (coordinateOrigin a) (Coord W) := by
    apply AlgHom.toLinearMap_injective
    apply TensorProduct.ext'
    intro x y
    change pullback (lift (toUnit W ≫ a.origin) (𝟙 W))
      ((tensorCoordinates (V := V) (W := W)).symm (x ⊗ₜ[k] y)) =
        coordinateOrigin a x • y
    have hx :
        pullback (lift (toUnit W ≫ a.origin) (𝟙 W)) (pullback (fst V W) x) =
          algebraMap k (Coord W) (coordinateOrigin a x) := by
      rw [← AlgHom.comp_apply, ← pullback_comp, lift_fst, pullback_constant_origin]
      rfl
    have hy :
        pullback (lift (toUnit W ≫ a.origin) (𝟙 W)) (pullback (snd V W) y) = y := by
      rw [← AlgHom.comp_apply, ← pullback_comp, lift_snd, pullback_id]
      rfl
    rw [tensorCoordinates_symm_tmul, map_mul, hx, hy, Algebra.smul_def]
  ext z
  have hh := DFunLike.congr_fun h ((tensorCoordinates (V := V) (W := W)) z)
  simpa using hh.symm

/-- The second coordinate identity slice is the pullback of the actual second
pointed slice under the actual tensor presentation. -/
theorem tensorCoordinates_rightIdentitySlice (a : PointedAction S W) :
    (rightIdentitySlice (Coord V) (coordinateOrigin a)).comp
        (tensorCoordinates (V := V) (W := W)).toAlgHom =
      pullback (lift (𝟙 V) (toUnit V ≫ a.origin)) := by
  have h :
      (pullback (lift (𝟙 V) (toUnit V ≫ a.origin))).comp
          (tensorCoordinates (V := V) (W := W)).symm.toAlgHom =
        rightIdentitySlice (Coord V) (coordinateOrigin a) := by
    apply AlgHom.toLinearMap_injective
    apply TensorProduct.ext'
    intro x y
    change pullback (lift (𝟙 V) (toUnit V ≫ a.origin))
      ((tensorCoordinates (V := V) (W := W)).symm (x ⊗ₜ[k] y)) =
        coordinateOrigin a y • x
    have hx :
        pullback (lift (𝟙 V) (toUnit V ≫ a.origin)) (pullback (fst V W) x) = x := by
      rw [← AlgHom.comp_apply, ← pullback_comp, lift_fst, pullback_id]
      rfl
    have hy :
        pullback (lift (𝟙 V) (toUnit V ≫ a.origin)) (pullback (snd V W) y) =
          algebraMap k (Coord V) (coordinateOrigin a y) := by
      rw [← AlgHom.comp_apply, ← pullback_comp, lift_snd, pullback_constant_origin]
      rfl
    rw [tensorCoordinates_symm_tmul, map_mul, hx, hy, Algebra.smul_def, mul_comm]
  ext z
  have hh := DFunLike.congr_fun h ((tensorCoordinates (V := V) (W := W)) z)
  simpa using hh.symm

end Langlands.GroupScheme.PointedCoordinateWeights

namespace Langlands.GroupScheme.RelativeRoot.CommutatorCoordinates

open PointedCoordinateWeights AugmentedTensor

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H K : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsAffineHom K.X.hom]

variable (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (d : AutomorphicAction S.toGrp K) (i : H ⟶ G) (j : K ⟶ G)
    (hi : ∀ {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S.X) (h : T ⟶ H.X),
      c.act s h ≫ i.hom.hom = b.act s (h ≫ i.hom.hom))
    (hj : ∀ {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S.X) (h : T ⟶ K.X),
      d.act s h ≫ j.hom.hom = b.act s (h ≫ j.hom.hom))

/-- The actual factor preserves the product action and its distinguished point. -/
theorem imageFactor_isPointedEquivariant :
    IsPointedEquivariant ((PointedAction.ofGroup c).prod (PointedAction.ofGroup d))
      (imageAction b c d i j hi hj) (imageFactor i j) := by
  constructor
  · intro T s v
    have he :
        ((PointedAction.ofGroup c).prod (PointedAction.ofGroup d)).act s v =
          lift (c.act s (v ≫ fst H.X K.X)) (d.act s (v ≫ snd H.X K.X)) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [he, imageFactor_equivariant b c d i j hi hj]
    simp
  · rfl

/-- Injectivity transports every nonzero augmentation weight of the actual
image to the actual input product. -/
theorem image_support_subset_product :
    support (imageAction b c d i j hi hj) ⊆
      support ((PointedAction.ofGroup c).prod (PointedAction.ofGroup d)) :=
  support_subset_of_injective _ _ (imageFactor i j)
    (imageFactor_isPointedEquivariant b c d i j hi hj)
    (imageFactor_pullback_injective i j)

omit b c d hi hj in
/-- The first identity slice of the actual factor is the constant image origin. -/
theorem imageFactor_left_identity_slice :
    lift (1 : K.X ⟶ H.X) (𝟙 K.X) ≫ imageFactor i j =
      toUnit K.X ≫ imageOrigin i j := by
  apply (cancel_mono (imageInclusion i j)).1
  rw [imageFactor_apply, Category.assoc, imageOrigin_comp]
  rw [← Hom.one_def]
  simp only [MonObj.one_comp, Category.id_comp, one_mul, inv_one, mul_one,
    mul_inv_cancel]

omit b c d hi hj in
/-- The second identity slice of the actual factor is the constant image origin. -/
theorem imageFactor_right_identity_slice :
    lift (𝟙 H.X) (1 : H.X ⟶ K.X) ≫ imageFactor i j =
      toUnit H.X ≫ imageOrigin i j := by
  apply (cancel_mono (imageInclusion i j)).1
  rw [imageFactor_apply, Category.assoc, imageOrigin_comp]
  rw [← Hom.one_def]
  simp only [MonObj.one_comp, Category.id_comp, inv_one, mul_one,
    mul_inv_cancel]

/-- The actual image pullback is constant at the image origin on the first
tensor-coordinate identity slice. -/
theorem imageFactor_tensor_leftIdentitySlice :
    (leftIdentitySlice (PointedCoordinateWeights.coordinateOrigin (PointedAction.ofGroup c))
        (Coord K.X)).comp
      ((PointedCoordinateWeights.tensorCoordinates (V := H.X) (W := K.X)).toAlgHom.comp
        (PointedCoordinateWeights.pullback (imageFactor i j))) =
      (Algebra.ofId k (Coord K.X)).comp
        (PointedCoordinateWeights.coordinateOrigin (imageAction b c d i j hi hj)) := by
  rw [← AlgHom.comp_assoc, tensorCoordinates_leftIdentitySlice, ← PointedCoordinateWeights.pullback_comp]
  change PointedCoordinateWeights.pullback
    (lift (1 : K.X ⟶ H.X) (𝟙 K.X) ≫ imageFactor i j) = _
  rw [imageFactor_left_identity_slice]
  exact pullback_constant_origin (imageAction b c d i j hi hj)

/-- The actual image pullback is constant at the image origin on the second
tensor-coordinate identity slice. -/
theorem imageFactor_tensor_rightIdentitySlice :
    (rightIdentitySlice (Coord H.X)
        (PointedCoordinateWeights.coordinateOrigin (PointedAction.ofGroup d))).comp
      ((PointedCoordinateWeights.tensorCoordinates (V := H.X) (W := K.X)).toAlgHom.comp
        (PointedCoordinateWeights.pullback (imageFactor i j))) =
      (Algebra.ofId k (Coord H.X)).comp
        (PointedCoordinateWeights.coordinateOrigin (imageAction b c d i j hi hj)) := by
  rw [← AlgHom.comp_assoc, tensorCoordinates_rightIdentitySlice, ← PointedCoordinateWeights.pullback_comp]
  change PointedCoordinateWeights.pullback
    (lift (𝟙 H.X) (1 : H.X ⟶ K.X) ≫ imageFactor i j) = _
  rw [imageFactor_right_identity_slice]
  exact pullback_constant_origin (imageAction b c d i j hi hj)

/-- The image augmentation ideal pulls back into the tensor of the two actual
input augmentation kernels. -/
theorem imageFactor_pullback_mem_augmentationTensor
    {z : Coord (imageScheme i j)}
    (hz : PointedCoordinateWeights.coordinateOrigin (imageAction b c d i j hi hj) z = 0) :
    (PointedCoordinateWeights.tensorCoordinates (V := H.X) (W := K.X))
        (PointedCoordinateWeights.pullback (imageFactor i j) z) ∈
      LinearMap.range (TensorProduct.mapIncl
        (augmentation (PointedAction.ofGroup c)) (augmentation (PointedAction.ofGroup d))) :=
  map_augmentationKernel_mem_tensor _ _ _ _
    (imageFactor_tensor_leftIdentitySlice b c d i j hi hj)
    (imageFactor_tensor_rightIdentitySlice b c d i j hi hj) hz

/-- A canonical linear factor of the actual image augmentation pullback through
the tensor of the two input augmentation kernels. -/
def imageAugmentationPullback :
    augmentation (imageAction b c d i j hi hj) →ₗ[k]
      augmentation (PointedAction.ofGroup c) ⊗[k] augmentation (PointedAction.ofGroup d) :=
  (TensorProduct.map
    (augmentationKernelProjection (PointedCoordinateWeights.coordinateOrigin (PointedAction.ofGroup c)))
    (augmentationKernelProjection (PointedCoordinateWeights.coordinateOrigin (PointedAction.ofGroup d)))).comp
      (((PointedCoordinateWeights.tensorCoordinates (V := H.X) (W := K.X)).toLinearMap.comp
        (PointedCoordinateWeights.pullback (imageFactor i j)).toLinearMap).domRestrict
          (augmentation (imageAction b c d i j hi hj)))

/-- Including this kernel tensor recovers the actual coordinate pullback. -/
theorem imageAugmentationPullback_include
    (z : augmentation (imageAction b c d i j hi hj)) :
    TensorProduct.mapIncl
        (augmentation (PointedAction.ofGroup c)) (augmentation (PointedAction.ofGroup d))
        (imageAugmentationPullback b c d i j hi hj z) =
      (PointedCoordinateWeights.tensorCoordinates (V := H.X) (W := K.X))
        (PointedCoordinateWeights.pullback (imageFactor i j) z) := by
  apply mapIncl_augmentationKernelProjection_eq
  · change leftIdentitySlice
      (PointedCoordinateWeights.coordinateOrigin (PointedAction.ofGroup c)) (Coord K.X)
      ((PointedCoordinateWeights.tensorCoordinates (V := H.X) (W := K.X))
        (PointedCoordinateWeights.pullback (imageFactor i j) z.val)) = 0
    have h := DFunLike.congr_fun (imageFactor_tensor_leftIdentitySlice b c d i j hi hj) z.val
    simpa only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
      show PointedCoordinateWeights.coordinateOrigin
      (imageAction b c d i j hi hj) z = 0 from z.property, map_zero] using h
  · change rightIdentitySlice (Coord H.X)
      (PointedCoordinateWeights.coordinateOrigin (PointedAction.ofGroup d))
      ((PointedCoordinateWeights.tensorCoordinates (V := H.X) (W := K.X))
        (PointedCoordinateWeights.pullback (imageFactor i j) z.val)) = 0
    have h := DFunLike.congr_fun (imageFactor_tensor_rightIdentitySlice b c d i j hi hj) z.val
    simpa only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
      show PointedCoordinateWeights.coordinateOrigin
      (imageAction b c d i j hi hj) z = 0 from z.property, map_zero] using h

end Langlands.GroupScheme.RelativeRoot.CommutatorCoordinates
