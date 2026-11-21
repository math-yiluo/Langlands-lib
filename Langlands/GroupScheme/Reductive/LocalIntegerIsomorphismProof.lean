import Langlands.GroupScheme.Reductive.GenericInnerIsomorphismReduction
import Langlands.GroupScheme.Reductive.GenericInnerIsomorphismTorsorExistenceProof

/-! # Generic isomorphisms extend after the adjoint action -/

universe u

namespace Langlands.GroupScheme

/-- A generic isomorphism of reductive groups over local integers extends
after precomposition by a point of the supplied generic adjoint quotient. -/
theorem reductiveLocalIntegerIsomorphism :
    ReductiveLocalIntegerIsomorphismStatement.{u} :=
  reductiveLocalIntegerIsomorphism_of_genericInnerIsomorphismTorsorExistence
    genericInnerIsomorphismTorsorExistence

end Langlands.GroupScheme
