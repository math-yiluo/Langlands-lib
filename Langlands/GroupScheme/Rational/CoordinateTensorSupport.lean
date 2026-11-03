import Langlands.GroupScheme.Rational.PointedTensorWeights
import Langlands.GroupScheme.Rational.AugmentedTensorSupport
import Mathlib.Algebra.DirectSum.Module

/-! # Literal tensor support for actual pointed affine coordinates -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open Classical
open scoped TensorProduct

namespace Langlands.GroupScheme.PointedCoordinateWeights

open RelativeRoot.AugmentedTensor

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {V W Z : Over (Spec (CommRingCat.of k))}
    [IsAffineHom V.hom] [IsAffineHom W.hom] [IsAffineHom Z.hom]

/-- Tensor degrees selected by one actual augmentation support character
from each factor, without adjoining the zero character. -/
def tensorSupportSpan (a : PointedAction S V) (b : PointedAction S W) :
    Submodule k (Coord V ⊗[k] Coord W) :=
  degreeSpan (tensorWeightSpace a b) (Set.image2 (· + ·) (support a) (support b))

/-- Spanning by actual augmentation weights puts the augmentation in the
selected coordinate degrees, without inserting the zero character. -/
theorem augmentation_le_degreeSpan_support (a : PointedAction S V)
    (ha : DirectSum.IsInternal (augmentationWeightSpace a)) :
    augmentation a ≤ degreeSpan (weightSpace a) (support a) := by
  have hs : (⨆ χ, (augmentationWeightSpace a χ).map (augmentation a).subtype) =
      augmentation a := by
    rw [← Submodule.map_iSup, ha.submodule_iSup_eq_top]
    simp
  rw [← hs]
  refine iSup_le fun χ => ?_
  rintro z ⟨w, hw, rfl⟩
  change (w : Coord V) ∈ degreeSpan (weightSpace a) (support a)
  by_cases hw0 : w = 0
  · simpa only [hw0, Submodule.coe_zero] using
      (degreeSpan (weightSpace a) (support a)).zero_mem
  · have hle : weightSpace a χ ≤ degreeSpan (weightSpace a) (support a) :=
      le_iSup_of_le χ
        (le_iSup_of_le (show χ ∈ support a from ⟨w, hw0, hw⟩) le_rfl)
    exact hle hw

/-- The actual product tensor eigenspaces satisfy the bilinear compatibility
required by the augmentation tensor calculation. -/
theorem tensor_weightSpace_compatible (a : PointedAction S V) (b : PointedAction S W)
    (α β : characterLattice S) :
    Submodule.map₂ (TensorProduct.mk k (Coord V) (Coord W))
      (weightSpace a α) (weightSpace b β) ≤ tensorWeightSpace a b (α + β) := by
  exact Submodule.map₂_le.mpr fun _ hx _ hy => tmul_mem_tensorWeightSpace a b hx hy

/-- Independence transports from the actual product coordinates to the actual
tensor coordinates. -/
theorem tensorWeightSpace_iSupIndep (a : PointedAction S V) (b : PointedAction S W)
    (hprod : DirectSum.IsInternal (weightSpace (a.prod b))) :
    iSupIndep (tensorWeightSpace a b) := by
  exact hprod.submodule_iSupIndep.map_orderIso
    (Submodule.orderIsoMapComap
      (tensorCoordinates (V := V) (W := W)).toLinearEquiv)

/-- The tensor of the two actual augmentation ideals has only literal sums
of input support characters, under the explicit input decompositions. -/
theorem tensor_augmentation_le_sum_degreeSpan
    (a : PointedAction S V) (b : PointedAction S W)
    (ha : DirectSum.IsInternal (augmentationWeightSpace a))
    (hb : DirectSum.IsInternal (augmentationWeightSpace b)) :
    LinearMap.range (TensorProduct.mapIncl (augmentation a) (augmentation b)) ≤
      tensorSupportSpan a b := by
  exact tensor_kernels_le_sum_degreeSpan
    (coordinateOrigin a) (coordinateOrigin b)
    (weightSpace a) (weightSpace b) (tensorWeightSpace a b) (support a) (support b)
    (augmentation_le_degreeSpan_support a ha)
    (augmentation_le_degreeSpan_support b hb)
    (tensor_weightSpace_compatible a b)

/-- A nonzero actual tensor eigenfunction killed by both identity slices has
a character in the literal sum of the input augmentation supports. -/
theorem weight_mem_sum_of_identity_slices
    (a : PointedAction S V) (b : PointedAction S W)
    (ha : DirectSum.IsInternal (augmentationWeightSpace a))
    (hb : DirectSum.IsInternal (augmentationWeightSpace b))
    (hprod : DirectSum.IsInternal (weightSpace (a.prod b)))
    {χ : characterLattice S} {z : Coord V ⊗[k] Coord W}
    (hz : z ≠ 0) (hχ : z ∈ tensorWeightSpace a b χ)
    (hleft : leftIdentitySlice (coordinateOrigin a) (Coord W) z = 0)
    (hright : rightIdentitySlice (Coord V) (coordinateOrigin b) z = 0) :
    χ ∈ Set.image2 (· + ·) (support a) (support b) := by
  apply degree_mem_of_nonzero (tensorWeightSpace_iSupIndep a b hprod) hz hχ
  apply tensor_augmentation_le_sum_degreeSpan a b ha hb
  change z ∈ LinearMap.range (TensorProduct.mapIncl
    (LinearMap.ker (coordinateOrigin a).toLinearMap)
    (LinearMap.ker (coordinateOrigin b).toLinearMap))
  rw [← ker_leftIdentitySlice_inf_ker_rightIdentitySlice]
  exact ⟨hleft, hright⟩

end Langlands.GroupScheme.PointedCoordinateWeights
