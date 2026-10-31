import Langlands.AbelianScheme.SubalgebraDescentStatements
import Langlands.AlgebraicGeometry.NoetherianApproximation.SubalgebraDescentStatements

/-! # Abelian-scheme descent from scheme, group-law and property descent -/

universe u

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.NoetherianApproximation

/-- Descent of finitely presented schemes, of group laws, and of separatedness, properness,
smoothness and geometric connectedness to finitely generated subalgebras implies the descent of
abelian schemes to finitely generated subrings. -/
def SubalgebraDescentReductionStatement : Prop :=
  SchemeSubalgebraDescentStatement.{u} →
    GroupScheme.SubalgebraDescentStatement.{u} →
      IsSeparatedSubalgebraDescentStatement.{u} →
        IsProperSubalgebraDescentStatement.{u} →
          SmoothSubalgebraDescentStatement.{u} →
            GeometricallyConnectedSubalgebraDescentStatement.{u} →
              Langlands.AbelianScheme.SubalgebraDescentStatement.{u}

end Langlands.AbelianScheme
