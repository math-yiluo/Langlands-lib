import Langlands.GroupScheme.Adjoint.RelativeExistenceProof
import Langlands.GroupScheme.Reductive.FiniteGenericOuterClassExistenceProof
import Langlands.GroupScheme.Reductive.GenericInnerIsomorphismTorsorExistenceReduction
import Langlands.GroupScheme.Reductive.GenericIsomorphismSchemeExistenceProof
import Langlands.GroupScheme.Reductive.GenericOuterIsomorphismSchemeExistenceProof

/-! # Existence of the integral inner-isomorphism torsor over a DVR -/

universe u

namespace Langlands.GroupScheme

/-- The prescribed generic isomorphism lies in an actual integral inner-isomorphism torsor. -/
theorem genericInnerIsomorphismTorsorExistence :
    GenericInnerIsomorphismTorsorExistenceStatement.{u} :=
  genericInnerIsomorphismTorsorExistence_of_affineQuotient_and_outerGeometry
    relativeAdjointQuotientExistence genericIsomorphismSchemeExistence
    genericOuterIsomorphismSchemeExistence finiteGenericOuterClassExistence

end Langlands.GroupScheme
