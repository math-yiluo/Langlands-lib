import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeCoefficientStatements
import Langlands.AlgebraicGeometry.PointTopology.AffineMapProofs
import Langlands.AlgebraicGeometry.PointTopology.AffineProductRingTopologyProof

/-!
# Proofs for coefficient change on actual affine scheme points
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

variable [TopologicalSpace S] [TopologicalSpace T]

theorem affineSchemeChangeRing_eq
    (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
    (f : S →ₐ[R] T) :
    RingPoint.changeRing (X := X) f =
      (affineSchemePointHomeomorph R X T).symm ∘
        AlgPoint.mapCoefficients f ∘ affineSchemePointHomeomorph R X S := by
  funext p
  apply (affineSchemePointEquiv R X T).injective
  change affineSchemePointEquiv R X T (p.changeRing f) =
    affineSchemePointEquiv R X T ((affineSchemePointEquiv R X T).symm
      (AlgPoint.mapCoefficients f (affineSchemePointEquiv R X S p)))
  rw [Equiv.apply_symm_apply, affineSchemePointEquiv_changeRing]

theorem affineSchemeCoefficientContinuity_proof :
    AffineSchemeCoefficientContinuityProperty R S T := by
  intro X _ f hf
  rw [affineSchemeChangeRing_eq R S T X f]
  exact (affineSchemePointHomeomorph R X T).symm.continuous.comp
    ((AlgPoint.continuous_mapCoefficients f hf).comp
      (affineSchemePointHomeomorph R X S).continuous)

theorem affineSchemeCoefficientEmbeddings_proof :
    AffineSchemeCoefficientEmbeddingProperties R S T := by
  intro X _ f
  constructor
  · intro hf
    rw [affineSchemeChangeRing_eq R S T X f]
    exact (affineSchemePointHomeomorph R X T).symm.isEmbedding.comp
      ((AlgPoint.isEmbedding_mapCoefficients f hf).comp
        (affineSchemePointHomeomorph R X S).isEmbedding)
  · intro hf
    rw [affineSchemeChangeRing_eq R S T X f]
    exact (affineSchemePointHomeomorph R X T).symm.isClosedEmbedding.comp
      ((AlgPoint.isClosedEmbedding_mapCoefficients f hf).comp
        (affineSchemePointHomeomorph R X S).isClosedEmbedding)

theorem affineSchemeCoefficientOpen_proof
    [IsTopologicalRing S] [IsTopologicalRing T] :
    AffineSchemeCoefficientOpenProperty R S T := by
  intro X _ _ f hf
  rw [affineSchemeChangeRing_eq R S T X f]
  exact (affineSchemePointHomeomorph R X T).symm.isOpenEmbedding.comp
    ((AlgPoint.isOpenEmbedding_mapCoefficients
      (inferInstance : Algebra.FiniteType R (AffineCoordinateRing R X)) f hf).comp
        (affineSchemePointHomeomorph R X S).isOpenEmbedding)

theorem affineSchemeDiscrete_proof
    [IsTopologicalRing S] [DiscreteTopology S] :
    AffineSchemeDiscreteProperty R S := by
  intro X _ _
  let : DiscreteTopology (AlgPoint R (AffineCoordinateRing R X) S) :=
    affineDiscreteProperty_proof
      (R := R) (A := AffineCoordinateRing R X) (S := S) inferInstance
  exact (affineSchemePointHomeomorph R X S).isEmbedding.discreteTopology

theorem affineSchemeCoefficientProperties_proof :
    AffineSchemeCoefficientProperties R S T := by
  refine ⟨affineSchemeCoefficientContinuity_proof R S T,
    affineSchemeCoefficientEmbeddings_proof R S T, ?_, ?_⟩
  · intro _ _
    exact affineSchemeCoefficientOpen_proof R S T
  · intro _ _
    exact affineSchemeDiscrete_proof R S

end Langlands.AlgebraicGeometry.PointTopology
