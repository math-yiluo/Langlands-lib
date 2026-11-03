import Langlands.GroupScheme.Rational.CoordinateTensorSupport

/-! # Actual product pullbacks with constant identity slices -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Classical
open scoped TensorProduct

namespace Langlands.GroupScheme.PointedCoordinateWeights

open RelativeRoot.AugmentedTensor

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {V W Z : Over (Spec (CommRingCat.of k))}
    [IsAffineHom V.hom] [IsAffineHom W.hom] [IsAffineHom Z.hom]

/-- The actual coordinate pullback of a product morphism in tensor coordinates. -/
def tensorPullback (f : V ⊗ W ⟶ Z) : Coord Z →ₐ[k] Coord V ⊗[k] Coord W :=
  (tensorCoordinates (V := V) (W := W)).toAlgHom.comp (pullback f)

theorem tensorPullback_injective (f : V ⊗ W ⟶ Z)
    (hf : Function.Injective (pullback f)) : Function.Injective (tensorPullback f) :=
  (tensorCoordinates (V := V) (W := W)).injective.comp hf

/-- Equivariance transports the actual all-test eigencondition through the
coordinate equivalence of the product. -/
theorem tensorPullback_mem_tensorWeightSpace
    (a : PointedAction S V) (b : PointedAction S W) (c : PointedAction S Z)
    (f : V ⊗ W ⟶ Z) (hf : IsPointedEquivariant (a.prod b) c f)
    {χ : characterLattice S} {z : Coord Z} (hz : z ∈ weightSpace c χ) :
    tensorPullback f z ∈ tensorWeightSpace a b χ :=
  ⟨pullback f z, pullback_mem_weightSpace (a.prod b) c f hf χ hz, rfl⟩

/-- An injective actual equivariant pullback, constant on both identity
slices, bounds the target augmentation support by the literal input sum. -/
theorem support_subset_sum_of_injective_constant_slices
    (a : PointedAction S V) (b : PointedAction S W) (c : PointedAction S Z)
    (f : V ⊗ W ⟶ Z) (hf : IsPointedEquivariant (a.prod b) c f)
    (hinj : Function.Injective (pullback f))
    (hleft : (leftIdentitySlice (coordinateOrigin a) (Coord W)).comp (tensorPullback f) =
      (Algebra.ofId k (Coord W)).comp (coordinateOrigin c))
    (hright : (rightIdentitySlice (Coord V) (coordinateOrigin b)).comp (tensorPullback f) =
      (Algebra.ofId k (Coord V)).comp (coordinateOrigin c))
    (ha : DirectSum.IsInternal (augmentationWeightSpace a))
    (hb : DirectSum.IsInternal (augmentationWeightSpace b))
    (hprod : DirectSum.IsInternal (weightSpace (a.prod b))) :
    support c ⊆ Set.image2 (· + ·) (support a) (support b) := by
  rintro χ ⟨z, hz, hχ⟩
  have hz0 : (z : Coord Z) ≠ 0 := fun h => hz (Subtype.ext h)
  have hφ0 : tensorPullback f (z : Coord Z) ≠ 0 := by
    intro h
    apply hz0
    exact tensorPullback_injective f hinj (h.trans (map_zero _).symm)
  apply weight_mem_sum_of_identity_slices a b ha hb hprod hφ0
    (tensorPullback_mem_tensorWeightSpace a b c f hf hχ)
  · change ((leftIdentitySlice (coordinateOrigin a) (Coord W)).comp
      (tensorPullback f)) (z : Coord Z) = 0
    rw [hleft, AlgHom.comp_apply, show coordinateOrigin c (z : Coord Z) = 0 from z.property,
      map_zero]
  · change ((rightIdentitySlice (Coord V) (coordinateOrigin b)).comp
      (tensorPullback f)) (z : Coord Z) = 0
    rw [hright, AlgHom.comp_apply, show coordinateOrigin c (z : Coord Z) = 0 from z.property,
      map_zero]

end Langlands.GroupScheme.PointedCoordinateWeights
