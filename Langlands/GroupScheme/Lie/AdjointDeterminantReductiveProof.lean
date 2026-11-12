import Langlands.GroupScheme.Lie.AdjointDeterminantReductiveStatement
import Langlands.GroupScheme.Reductive.CentralDerivedProductReduction
import Langlands.GroupScheme.Derived.RepresentabilityProof
import Langlands.GroupScheme.Reductive.CentralTorusSurjectivityProof

/-! # connectedReductiveAdjointDeterminant: unconditional proof from published reductions -/

universe u

namespace Langlands.GroupScheme.Lie

/-- The actual rational adjoint determinant character is zero for every connected reductive affine locally finite-type group over every field. -/
theorem connectedReductiveAdjointDeterminant :
    ConnectedReductiveAdjointDeterminantStatement.{u} :=
  connectedReductiveAdjointDeterminant_of_centralDerivedProduct
    (reductiveCentralDerivedProduct_of_surjectivity derivedSubgroupRepresentability
      reductiveCentralTorusSurjectivity)

end Langlands.GroupScheme.Lie
