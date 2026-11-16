import Langlands.AlgebraicGeometry.Picard.FieldRigidifiedPicardRepresentabilityStatement
import Langlands.AlgebraicGeometry.Picard.FieldRigidifiedPicardRepresentabilityReduction
import Langlands.AlgebraicGeometry.Picard.FiniteTypeFormalVersalBundleProof
import Langlands.CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationProof

/-! # Full rigidified Picard representability over a field: proof -/

universe u

namespace Langlands.AbelianScheme

/-- Every abelian variety over an arbitrary field has an actual universal rigidified
line bundle on a parameter scheme locally of finite type over the field. The two
inputs of the published reduction, formally versal Picard families and finite-order
etale approximation over finite-type `ℤ`-algebras, are both published proofs. -/
theorem fieldRigidifiedPicardRepresentability :
    FieldRigidifiedPicardRepresentabilityStatement.{u} :=
  fieldRigidifiedPicardRepresentability_of_formalVersal_of_etaleApproximation
    Langlands.AlgebraicGeometry.Picard.finiteTypeFormalVersalBundle
    Langlands.CommutativeAlgebra.finiteTypeIntEtaleCompletionApproximation

end Langlands.AbelianScheme
