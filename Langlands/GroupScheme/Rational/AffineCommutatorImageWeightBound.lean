import Langlands.GroupScheme.Rational.AffineCommutatorImageSupport
import Langlands.GroupScheme.Rational.PointedTensorPullback
import Langlands.GroupScheme.Rational.PointedCoordinateDecompositionProof
import Langlands.GroupScheme.Rational.WeightSemigroupStatement

/-! # Literal augmentation weight bound for the actual commutator image -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

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

/-- The canonical augmentation tensor pullback is injective. -/
theorem imageAugmentationPullback_injective :
    Function.Injective (imageAugmentationPullback b c d i j hi hj) := by
  intro x y h
  apply Subtype.ext
  apply imageFactor_pullback_injective i j
  apply (PointedCoordinateWeights.tensorCoordinates (V := H.X) (W := K.X)).injective
  rw [← imageAugmentationPullback_include b c d i j hi hj x,
    ← imageAugmentationPullback_include b c d i j hi hj y, h]

/-- The actual image augmentation is linearly identified with its canonical
range in the tensor of the two input augmentation kernels. -/
def imageAugmentationRangeEquiv :
    augmentation (imageAction b c d i j hi hj) ≃ₗ[k]
      LinearMap.range (imageAugmentationPullback b c d i j hi hj) :=
  LinearEquiv.ofInjective _ (imageAugmentationPullback_injective b c d i j hi hj)

open Classical in
/-- Under explicit weight decompositions, the actual commutator image has
only literal sums of input augmentation weights. -/
theorem image_support_subset_sum_of_decompositions
    (hc : DirectSum.IsInternal (augmentationWeightSpace (PointedAction.ofGroup c)))
    (hd : DirectSum.IsInternal (augmentationWeightSpace (PointedAction.ofGroup d)))
    (hprod : DirectSum.IsInternal
      (PointedCoordinateWeights.weightSpace
        ((PointedAction.ofGroup c).prod (PointedAction.ofGroup d)))) :
    support (imageAction b c d i j hi hj) ⊆
      Set.image2 (· + ·) (CoordinateWeights.support c) (CoordinateWeights.support d) := by
  simpa only [ofGroup_support] using
    support_subset_sum_of_injective_constant_slices
      (PointedAction.ofGroup c) (PointedAction.ofGroup d) (imageAction b c d i j hi hj)
      (imageFactor i j) (imageFactor_isPointedEquivariant b c d i j hi hj)
      (imageFactor_pullback_injective i j)
      (imageFactor_tensor_leftIdentitySlice b c d i j hi hj)
      (imageFactor_tensor_rightIdentitySlice b c d i j hi hj) hc hd hprod

/-- For an actual split torus, every augmentation weight of the actual closed
commutator image is a sum of one augmentation weight from each input group. -/
theorem image_support_subset_sum (hS : IsSplitTorus S.toGrp) :
    support (imageAction b c d i j hi hj) ⊆
      Set.image2 (· + ·) (CoordinateWeights.support c) (CoordinateWeights.support d) := by
  classical
  apply image_support_subset_sum_of_decompositions b c d i j hi hj
  · exact (pointedCoordinateDecomposition k S hS H.X (PointedAction.ofGroup c)).2
  · exact (pointedCoordinateDecomposition k S hS K.X (PointedAction.ofGroup d)).2
  · exact (pointedCoordinateDecomposition k S hS (H.X ⊗ K.X)
      ((PointedAction.ofGroup c).prod (PointedAction.ofGroup d))).1

/-- Input augmentation-support bounds give the corresponding literal
semigroup-sum bound on the actual image augmentation support. -/
theorem image_support_subset_semigroupSum (hS : IsSplitTorus S.toGrp)
    (A A' : AddSubsemigroup (characterLattice S))
    (hc : CoordinateWeights.support c ⊆ A) (hd : CoordinateWeights.support d ⊆ A') :
    support (imageAction b c d i j hi hj) ⊆ semigroupSum A A' := by
  intro χ hχ
  obtain ⟨α, hα, β, hβ, hsum⟩ := image_support_subset_sum b c d i j hi hj hS hχ
  exact ⟨α, hc hα, β, hd hβ, hsum⟩

end Langlands.GroupScheme.RelativeRoot.CommutatorCoordinates
