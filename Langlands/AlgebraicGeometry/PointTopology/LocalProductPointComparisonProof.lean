import Langlands.AlgebraicGeometry.PointTopology.LocalProductPointComparisonStatement
import Langlands.AlgebraicGeometry.PointTopology.ProductRingPointComparisonProof
import Langlands.AlgebraicGeometry.PointTopology.AffineProductRingTopologyProof
import Langlands.AlgebraicGeometry.PointTopology.AffineBaseChangeTopologyProof

/-!
# Proof of the comparison with actual base-changed local models

Compose the relative product comparison with the factorwise actual
pullback-adjunction equivalence, including its affine topology comparison.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (C : Type u) [CommRing C] {ι : Type u} (R : ι → Type u)
variable [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)]
variable (X : Over (Spec (CommRingCat.of C)))

theorem localProductPointMap_injective [QuasiSeparatedSpace X.left] :
    Function.Injective (localProductPointMap C R X) :=
  (localFactorPointEquiv C R X).injective.comp (productPointMap_injective C R X)

theorem localProductPointMap_surjective_of_isAffine [IsAffine X.left] :
    Function.Surjective (localProductPointMap C R X) :=
  (localFactorPointEquiv C R X).surjective.comp
    (productPointMap_surjective_of_isAffine C R X)

theorem localProductPointMap_surjective [CompactSpace X.left] [∀ i, IsLocalRing (R i)] :
    Function.Surjective (localProductPointMap C R X) :=
  (localFactorPointEquiv C R X).surjective.comp (productPointMap_surjective C R X)

theorem localProductPointMap_isHomeomorph
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [IsAffine X.left] :
    IsHomeomorph (localProductPointMap C R X) := by
  have h : IsHomeomorph (localFactorPointEquiv C R X) :=
    IsHomeomorph.pi_map (fun i =>
      isHomeomorph_ringPointBaseChangeEquiv C (R i) (R i) X)
  exact h.comp (productPointMap_isHomeomorph C R X)

/-- The exact four-clause comparison with the existing actual local-model map. -/
theorem localProductPointComparison : LocalProductPointComparisonStatement.{u} := by
  intro C _ ι R _ _ X
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hQS
    exact localProductPointMap_injective C R X
  · intro hAffine
    exact localProductPointMap_surjective_of_isAffine C R X
  · intro hCompact hLocal
    exact localProductPointMap_surjective C R X
  · intro hTopology hTopologicalRing hAffine
    exact localProductPointMap_isHomeomorph C R X

end Langlands.AlgebraicGeometry.PointTopology
