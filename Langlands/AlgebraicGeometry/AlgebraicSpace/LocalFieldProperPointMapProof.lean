import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalFieldProperPointValuativeReductionProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceValuativeExistenceProof

/-! # Corollary 5.6 for algebraic spaces: proof -/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- **Conrad, Corollary 5.6, for algebraic spaces.** For a proper morphism of quasi-separated
algebraic spaces locally of finite type over a locally compact nontrivially normed field `K`,
the induced map on `K`-points is proper for the étale-chart topologies. -/
theorem localFieldProperPointMap : LocalFieldProperPointMapStatement.{u} :=
  localFieldProperPointValuativeReduction spaceValuativeExistence

end Langlands.AlgebraicGeometry.AlgebraicSpace
