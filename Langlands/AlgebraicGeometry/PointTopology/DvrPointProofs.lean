import Langlands.AlgebraicGeometry.PointTopology.DvrPointStatements
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeCoefficientProofs

/-!
# Open and closed embeddings of actual DVR-valued affine points
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open scoped WithZero

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

theorem dvrAffinePointProperties_proof : DvrAffinePointProperties R K := by
  let : Valued K ℤᵐ⁰ := Valued.mk' ((IsDiscreteValuationRing.maximalIdeal R).valuation K)
  let : TopologicalSpace R := TopologicalSpace.induced (algebraMap R K) inferInstance
  have he : IsEmbedding (algebraMap R K) :=
    ⟨⟨rfl⟩, IsFractionRing.injective R K⟩
  have hr : Set.range (algebraMap R K) =
      (((IsDiscreteValuationRing.maximalIdeal R).valuation K).valuationSubring : Set K) := by
    ext x
    change (∃ a, algebraMap R K a = x) ↔
      ((IsDiscreteValuationRing.maximalIdeal R).valuation K) x ≤ 1
    constructor
    · rintro ⟨a, rfl⟩
      exact (IsDiscreteValuationRing.maximalIdeal R).valuation_le_one a
    · exact IsDiscreteValuationRing.exists_lift_of_le_one
  have ho : IsOpenEmbedding (Algebra.ofId R K) := by
    refine ⟨he, ?_⟩
    change IsOpen (Set.range (algebraMap R K))
    rw [hr]
    exact Valued.isOpen_valuationSubring K
  have hc : IsClosedEmbedding (Algebra.ofId R K) := by
    refine ⟨he, ?_⟩
    change IsClosed (Set.range (algebraMap R K))
    rw [hr]
    exact Valued.isClosed_valuationSubring K
  intro X _ _
  rw [affineSchemeChangeRing_eq R R K X (Algebra.ofId R K)]
  constructor
  · exact (affineSchemePointHomeomorph R X K).symm.isOpenEmbedding.comp
      ((AlgPoint.isOpenEmbedding_mapCoefficients
        (inferInstance : Algebra.FiniteType R (AffineCoordinateRing R X))
          (Algebra.ofId R K) ho).comp
        (affineSchemePointHomeomorph R X R).isOpenEmbedding)
  · exact (affineSchemePointHomeomorph R X K).symm.isClosedEmbedding.comp
      ((AlgPoint.isClosedEmbedding_mapCoefficients (Algebra.ofId R K) hc).comp
        (affineSchemePointHomeomorph R X R).isClosedEmbedding)

end Langlands.AlgebraicGeometry.PointTopology
