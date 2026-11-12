import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionTensorPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceFiniteProductSections

/-! # Tensor Weil point equivalence over finite products of arbitrary rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

section FiniteProduct

variable (B : Type u) [CommRing B]
  (X : AlgebraicSpace (Spec (CommRingCat.of B)))
  {ι : Type u} [Finite ι] (D : ι → Type u)
  [∀ i, CommRing (D i)] [∀ i, Algebra B (D i)]

/-- An algebraic space takes a finite product of coefficient rings to
the product of its original ring-valued point sets. -/
def finiteProductRingPointsEquiv :
    RingPoints B X (∀ i, D i) ≃ (∀ i, RingPoints B X (D i)) :=
  FppfCoproduct.sectionsEquiv X.toSheaf (fun i => ringTest B (D i))
    (ringTest B (∀ i, D i)) (fun i => ringTestMap B (Pi.evalAlgHom B D i))
    (((Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
      (Cofan.mk (Spec (CommRingCat.of (∀ i, D i)))
        (finiteProductSpecProjection D))).mpr
      (inferInstanceAs (IsIso (sigmaSpec (fun i => CommRingCat.of (D i)))))).some)

@[simp]
theorem finiteProductRingPointsEquiv_apply
    (x : RingPoints B X (∀ i, D i)) (i : ι) :
    finiteProductRingPointsEquiv B X D x i =
      RingPoints.changeRing (Pi.evalAlgHom B D i) x := rfl

end FiniteProduct

section Tensor

variable (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C]
  {ι : Type u} [Finite ι] (D : ι → Type u)
  [∀ i, CommRing (D i)] [∀ i, Algebra C (D i)] [∀ i, Algebra B (D i)]
  (e : C ⊗[R] B ≃ₐ[C] (∀ i, D i))
  (he : ∀ (b : B) (i : ι), e (1 ⊗ₜ[R] b) i = algebraMap B (D i) b)
  (X : AlgebraicSpace (Spec (CommRingCat.of B)))
  (h : IsAlgebraicSpace _ ((ringWeilRestriction R B).obj X.toSheaf))

/-- The canonical tensor factor map is an equivalence for arbitrary
commutative factor rings, including completed valuation rings. -/
def completedTensorSpaceWeilRestrictionPointsEquiv :
    RingPoints R (ringWeilRestrictionSpace R B X h) C ≃
      (∀ i, RingPoints B X (D i)) :=
  (ringWeilRestrictionTensorPointsEquiv R B C (∀ i, D i) e
    (fun b => funext (he b)) X h).trans (finiteProductRingPointsEquiv B X D)

@[simp]
theorem completedTensorSpaceWeilRestrictionPointsEquiv_apply
    (x : RingPoints R (ringWeilRestrictionSpace R B X h) C) (i : ι) :
    completedTensorSpaceWeilRestrictionPointsEquiv R B C D e he X h x i =
      completedTensorSpaceWeilRestrictionPointMap R B C D e he X h x i :=
  (completedTensorSpaceWeilRestrictionPointMap_eq R B C D e he X h x i).symm

/-- Bijectivity of the original factor map requires only algebraicity
of the original Weil restriction and the supplied finite-product tensor
decomposition. -/
theorem completedTensorSpaceWeilRestrictionPointMap_bijective :
    Function.Bijective (completedTensorSpaceWeilRestrictionPointMap R B C D e he X h) := by
  have heq : (completedTensorSpaceWeilRestrictionPointsEquiv R B C D e he X h :
      RingPoints R (ringWeilRestrictionSpace R B X h) C →
        ∀ i, RingPoints B X (D i)) =
      completedTensorSpaceWeilRestrictionPointMap R B C D e he X h :=
    funext fun x => funext fun i =>
      completedTensorSpaceWeilRestrictionPointsEquiv_apply R B C D e he X h x i
  rw [← heq]
  exact (completedTensorSpaceWeilRestrictionPointsEquiv R B C D e he X h).bijective

end Tensor

end Langlands.AlgebraicGeometry.AlgebraicSpace
