import Langlands.AlgebraicGeometry.Picard.FieldDualSchemeExistenceStatement
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Existence of the universal Picard-zero family over a quasi-separated base -/

universe u

open AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- An abelian scheme over a quasi-separated base has an actual universal
geometric Picard-zero family, classifying families on every test scheme. -/
def RelativeDualSchemeExistenceStatement : Prop :=
  ∀ (S : Scheme.{u}) [QuasiSeparatedSpace S] (A : AbelianScheme S), HasDualScheme A

/-- The relative existence target specializes to the existing field target. -/
lemma RelativeDualSchemeExistenceStatement.field
    (existence : RelativeDualSchemeExistenceStatement.{u}) :
    FieldDualSchemeExistenceStatement.{u} := by
  intro k _ A
  exact existence _ A

end Langlands.AbelianScheme
