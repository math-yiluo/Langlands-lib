import Langlands.GroupScheme.Absolute.SolvableTorusQuotientReduction
import Langlands.GroupScheme.Absolute.TriangularDiagonalKernelGeometryProof
import Langlands.GroupScheme.UnipotentClosedSubgroupProof

/-! # The split-torus quotient of a smooth connected solvable group -/

universe u

namespace Langlands.GroupScheme

/-- Every smooth connected affine solvable group over an algebraically closed field has a
smooth connected unipotent normal closed subgroup with an actual fppf split-torus quotient. -/
theorem solvableTorusQuotient : SolvableTorusQuotientStatement.{u} :=
  solvableTorusQuotient_of_kernel_prerequisites triangularDiagonalKernelGeometry
    unipotentClosedSubgroup

end Langlands.GroupScheme
