import Langlands.GroupScheme.Reductive.SemisimpleIdentityComponent.Reduction
import Langlands.GroupScheme.Reductive.SemisimpleRepresentationCharZeroProof
import Langlands.GroupScheme.Reductive.SemisimpleFieldExtensionReduction
import Langlands.Algebra.SemisimpleScalarExtensionProof

/-! # Semisimple representations and the identity component in characteristic zero (proof) -/

universe u

namespace Langlands.GroupScheme

/-- **Milne, *Algebraic Groups* (2017), Corollaries 22.43 and 22.44.** For an affine group
scheme of finite type over a field of characteristic zero, every finite-dimensional
representation is semisimple exactly when the identity component is reductive, and then
tensor products of semisimple representations are semisimple.

The proof combines the published conditional reduction
`SemisimpleIdentityComponent.charZeroSemisimpleRepresentationIdentityComponent_of` with the
published proofs of its two hypotheses: Milne 22.42 (`charZeroReductiveSemisimpleRepresentation`)
and Milne 4.19 (`semisimpleRepresentationFieldExtension_of_algebra` applied to the generic
algebra theorem `Langlands.Algebra.semisimpleScalarExtension`). -/
theorem charZeroSemisimpleRepresentationIdentityComponent :
    CharZeroSemisimpleRepresentationIdentityComponentStatement.{u} :=
  SemisimpleIdentityComponent.charZeroSemisimpleRepresentationIdentityComponent_of
    charZeroReductiveSemisimpleRepresentation
    (semisimpleRepresentationFieldExtension_of_algebra
      Langlands.Algebra.semisimpleScalarExtension.{u,u,u})

end Langlands.GroupScheme
