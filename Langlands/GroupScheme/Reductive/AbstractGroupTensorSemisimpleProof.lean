import Langlands.Algebra.SemisimpleScalarExtensionProof
import Langlands.GroupScheme.Reductive.AbstractGroupTensorSemisimpleStatement
import Langlands.GroupScheme.Reductive.FiniteCoordinateEnvelopes
import Langlands.GroupScheme.Reductive.SemisimpleFieldExtensionReduction
import Langlands.GroupScheme.Reductive.SemisimpleIdentityComponent.Reduction
import Langlands.GroupScheme.Reductive.SemisimpleRepresentationCharZeroProof

/-! # Tensor products of semisimple representations of abstract groups in characteristic zero -/

universe u v w₁ w₂

namespace Langlands.GroupScheme

/-- Over a field of characteristic zero, the tensor product of semisimple
finite-dimensional representations of an abstract group is semisimple
(Milne, *Algebraic Groups*, Corollary 22.45). -/
theorem charZeroAbstractGroupTensorSemisimple :
    CharZeroAbstractGroupTensorSemisimpleStatement.{u, v, w₁, w₂} := by
  have halgebraic : CharZeroSemisimpleRepresentationIdentityComponentStatement.{u} :=
    SemisimpleIdentityComponent.charZeroSemisimpleRepresentationIdentityComponent_of
      charZeroReductiveSemisimpleRepresentation
      (semisimpleRepresentationFieldExtension_of_algebra
        Langlands.Algebra.semisimpleScalarExtension.{u, u, u})
  exact AbstractGroupTensorReduction.abstractGroupTensorSemisimple_of_envelopes
    halgebraic (fun k _ _ G _ => AbstractGroupTensorReduction.hasFiniteCoordinateEnvelopes k G)

end Langlands.GroupScheme
