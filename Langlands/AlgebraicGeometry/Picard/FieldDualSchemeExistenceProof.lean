import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeExistenceStatement
import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeExistenceReduction
import Langlands.AlgebraicGeometry.Picard.FieldRigidifiedPicardRepresentabilityProof

/-! # Existence of the universal geometric Picard-zero family over a field: proof -/

universe u

namespace Langlands.AbelianScheme

/-- Every abelian scheme over the spectrum of an arbitrary field has an actual universal
geometric Picard-zero family. The published reduction restricts the universal rigidified
family to its open Picard-zero locus; full rigidified Picard representability over fields
is a published proof. -/
theorem fieldDualSchemeExistence : FieldDualSchemeExistenceStatement.{u} :=
  fieldDualSchemeExistence_of_rigidifiedRepresentability
    fieldRigidifiedPicardRepresentability

end Langlands.AbelianScheme
