import Langlands.AlgebraicGeometry.Picard.AbelianSchemeNoetherianModelStatement
import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleDescentStatements
import Langlands.AbelianScheme.SubalgebraDescentStatements

/-! # Noetherian models from abelian-scheme and line-bundle descent -/

universe u

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.NoetherianApproximation

/-- Descent of abelian schemes, of line bundles and of isomorphisms of line bundles to finitely
generated subalgebras implies the existence of noetherian models of an abelian scheme with two
rigidified line bundles. -/
def AbelianSchemeNoetherianModelReductionStatement : Prop :=
  Langlands.AbelianScheme.SubalgebraDescentStatement.{u} →
    LineBundleSubalgebraDescentStatement.{u} →
      LineBundleIsoSubalgebraDescentStatement.{u} →
        AbelianSchemeNoetherianModelStatement.{u}

end Langlands.AbelianScheme
