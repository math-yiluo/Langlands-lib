import Langlands.GroupScheme.Rational.LocalFieldLinearTopologyStatement
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup

/-! # The canonical local-field rational-point topology is the linear-subgroup topology -/

universe u

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The canonical evaluation topology compares with every closed linear
embedding through the actual general-linear matrix points. -/
theorem localFieldLinearTopology : LocalFieldLinearTopologyStatement.{u} := by
  intro F _ _ _ _ G _ _
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : T2Space F := BruhatTits.localField_t2Space F
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  refine ⟨rationalPoint_isTopologicalGroup F G, rationalPoint_t2Space F G,
    rationalPoint_locallyCompactSpace F G, rationalPoint_totallyDisconnectedSpace_of_localField F G.X,
    affineLinearEmbeddingStatement F G inferInstance inferInstance, ?_⟩
  intro N ρ hρ
  let H := GeneralLinear.groupScheme (Fin N) (CommRingCat.of F)
  let : IsAffine H.X.left := GeneralLinear.isAffine_groupScheme (Fin N) (CommRingCat.of F)
  let : TopologicalSpace (rationalPoints H) := rationalPointTopology F H.X
  let : IsClosedImmersion ρ.hom.hom.left := hρ
  have hpoints := isClosedEmbedding_rationalPointMap F ρ.hom.hom
  exact (GeneralLinear.rationalPointsContinuousMulEquiv N F).toHomeomorph.isClosedEmbedding.comp hpoints

end Langlands.GroupScheme
