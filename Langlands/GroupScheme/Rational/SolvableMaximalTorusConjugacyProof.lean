import Langlands.GroupScheme.Rational.SolvableMaximalTorusQuotientAssembly
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientReduction
import Langlands.GroupScheme.Absolute.TriangularDiagonalKernelGeometryProof
import Langlands.GroupScheme.UnipotentClosedSubgroupProof

/-! # Rational conjugacy of maximal tori in smooth connected solvable groups -/

universe u

namespace Langlands.GroupScheme

/-- Over every field, maximal tori of a smooth connected affine solvable group
are conjugate by a rational point, with an isomorphism of their sources. -/
theorem solvableMaximalTorusConjugacy :
    SolvableMaximalTorusConjugacyStatement.{u} :=
  solvableMaximalTorusConjugacy_of_torusQuotient
    (solvableTorusQuotient_of_kernel_prerequisites
      triangularDiagonalKernelGeometry unipotentClosedSubgroup)

end Langlands.GroupScheme
