import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyExistence
import Langlands.AlgebraicGeometry.PointTopology.AffineTopologyUniqueness

/-!
# Characterization of the evaluation topology on actual affine scheme points
-/

universe u

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S] [IsTopologicalRing S]

theorem affineSchemeTopology_eq_evaluation
    (T : AffineSchemeTopologyFamily R S) (hT : AffineSchemeTopologyAxioms R S T) :
    T = evaluationAffineSchemeTopologyFamily R S := by
  have hcoord := affineTopologyUniqueness_proof R S
    (schemeTopologyFamilyToAlgebras R S T) (schemeTopology_toAlgebras_axioms R S T hT)
  calc
    T = algebraTopologyFamilyToSchemes R S (schemeTopologyFamilyToAlgebras R S T) :=
      (affineSchemeTopology_transport_recover R S T hT.1).symm
    _ = algebraTopologyFamilyToSchemes R S (evaluationAffineTopologyFamily R S) :=
      congrArg (algebraTopologyFamilyToSchemes R S) hcoord
    _ = evaluationAffineSchemeTopologyFamily R S := evaluationAlgebraTopology_toSchemes R S

theorem affineSchemeTopologyCharacterization_proof :
    AffineSchemeTopologyCharacterizationProperty R S := by
  intro T
  constructor
  · exact affineSchemeTopology_eq_evaluation R S T
  · intro hT
    subst T
    exact affineSchemeTopologyExistence_proof R S

end Langlands.AlgebraicGeometry.PointTopology
