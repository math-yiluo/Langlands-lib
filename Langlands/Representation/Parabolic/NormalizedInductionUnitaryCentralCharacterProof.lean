import Langlands.Representation.Parabolic.NormalizedInductionUnitaryCentralCharacterStatement
import Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof

/-!
# The full unitary central character of actual normalized induction

The supplied Levi character, restricted to the common block scalars, is a
scalar character of the Levi representation. The published scalar-action
theorem for normalized parabolic induction transfers it to the ambient scalar
matrices, and the published full-center constructor pulls the Levi character
back along the diagonal-block projection of the full ambient center.
-/

namespace Langlands

universe uF uV

/-- Actual normalized upper parabolic induction carries the full-center pullback
of every supplied unitary central character of the inducing Levi representation. -/
theorem glNormalizedInductionUnitaryCentralCharacter :
    GLNormalizedInductionUnitaryCentralCharacterStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro n B
  let := T.generalLinearTopologicalGroup n
  intro V _ _ σ c
  have hω : Classification.HasScalarCharacter σ (B.scalarLevi F.Carrier)
      (c.character.comp (B.diagonalScalarToCenter F.Carrier)) :=
    fun a v => c.acts (B.diagonalScalarToCenter F.Carrier a) v
  exact ⟨B.unitaryCentralCharacterOfLeviScalar F.Carrier σ c
    (T.normalizedParabolicInduced B σ) (T.hasScalarCharacter_normalizedParabolicInduced B hω),
    fun _ => rfl⟩

end Langlands
