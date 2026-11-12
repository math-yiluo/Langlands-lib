import Langlands.Representation.Aubert.General.RationalGeometricK0Assembly
import Langlands.GroupScheme.Rational.StandardParabolicPointsProof

/-!
# Proof of the rational geometric-lemma K0 expansion

The published target `RationalGeometricK0ExpansionStatement` follows from its
reduction to `StandardParabolicPointsStatement` and the published proof of that
statement.
-/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- **The geometric lemma on exact K0** for the actual rational-point families of
every connected reductive group over every nonarchimedean local field: the exact
published `RationalGeometricK0ExpansionStatement`, at independent universes. -/
theorem rationalGeometricK0Expansion : RationalGeometricK0ExpansionStatement.{u, v} :=
  rationalGeometricK0Expansion_of_standardParabolicPoints.{u, v}
    GroupScheme.standardParabolicPointsStatement_proof.{u}

end Langlands.Aubert.General.RationalPointFamily
