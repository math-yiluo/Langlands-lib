import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMapStatements
import Langlands.AlgebraicGeometry.PointTopology.AffineProofs

/-!
# Mapping proofs for actual affine scheme points
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable {X Y : Over (Spec (CommRingCat.of R))} [IsAffine X.left] [IsAffine Y.left]
variable [TopologicalSpace S]

theorem affineSchemePointMap_eq (f : X ⟶ Y) :
    (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S)) =
      (affineSchemePointHomeomorph R Y S).symm ∘
        AlgPoint.precomp (affineCoordinatePullback R f) ∘
          affineSchemePointHomeomorph R X S := by
  funext p
  apply (affineSchemePointEquiv R Y S).injective
  change affineSchemePointEquiv R Y S (p ≫ f) =
    (affineSchemePointEquiv R Y S)
      ((affineSchemePointEquiv R Y S).symm
        (AlgPoint.precomp (affineCoordinatePullback R f)
          (affineSchemePointEquiv R X S p)))
  rw [Equiv.apply_symm_apply]
  exact affineSchemePointEquiv_natural R S f p

theorem continuous_affineSchemePointMap (f : X ⟶ Y) :
    Continuous (X := RingPoint R X S) (Y := RingPoint R Y S)
      (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S)) := by
  rw [affineSchemePointMap_eq R S f]
  exact (affineSchemePointHomeomorph R Y S).symm.continuous.comp
    ((AlgPoint.continuous_precomp _).comp
      (affineSchemePointHomeomorph R X S).continuous)

theorem isEmbedding_affineSchemePointMap (f : X ⟶ Y) [IsClosedImmersion f.left] :
    IsEmbedding (X := RingPoint R X S) (Y := RingPoint R Y S)
      (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S)) := by
  have hs : Function.Surjective (affineCoordinatePullback R f) :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine f.left).2
  rw [affineSchemePointMap_eq R S f]
  exact (affineSchemePointHomeomorph R Y S).symm.isEmbedding.comp
    ((AlgPoint.isEmbedding_precomp_of_surjective _ hs).comp
      (affineSchemePointHomeomorph R X S).isEmbedding)

theorem isClosedEmbedding_affineSchemePointMap [T2Space S]
    (f : X ⟶ Y) [IsClosedImmersion f.left] :
    IsClosedEmbedding (X := RingPoint R X S) (Y := RingPoint R Y S)
      (fun p : RingPoint R X S => (p ≫ f : RingPoint R Y S)) := by
  have hs : Function.Surjective (affineCoordinatePullback R f) :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine f.left).2
  rw [affineSchemePointMap_eq R S f]
  exact (affineSchemePointHomeomorph R Y S).symm.isClosedEmbedding.comp
    ((AlgPoint.isClosedEmbedding_precomp_of_surjective _ hs).comp
      (affineSchemePointHomeomorph R X S).isClosedEmbedding)

theorem affineSchemeMapProperties_proof :
    AffineSchemeMapProperties R S X Y := by
  refine ⟨continuous_affineSchemePointMap R S, ?_⟩
  intro f hf
  refine ⟨isEmbedding_affineSchemePointMap R S f, ?_⟩
  intro hT2
  exact isClosedEmbedding_affineSchemePointMap R S f

end Langlands.AlgebraicGeometry.PointTopology
