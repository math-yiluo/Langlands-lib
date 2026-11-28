import Langlands.BaseChange.SupercuspidalCoefficientEllipticMatchingStatement
import Langlands.BaseChange.SupercuspidalWindowCoefficientCuspFormStatement
import Langlands.BaseChange.SupercuspidalWindowSchurOrthogonalityStatement
import Langlands.BaseChange.SupercuspidalCoefficientEllipticOrbitalStatement

/-!
# Elliptic matching of supercuspidal coefficients from three analytic statements

The implication from three statements about cut-off coefficients of supercuspidal
representations of `GL_n` (they are cusp forms, Schur orthogonality, and their twisted elliptic
orbital integrals) to `SupercuspidalCoefficientEllipticMatchingStatement`. Statement only; see
the paired Markdown.
-/

namespace Langlands.BaseChange

/-- `SupercuspidalCoefficientEllipticMatchingStatement.{u, v, uV, uW}` follows from
`SupercuspidalWindowCoefficientCuspFormStatement`, `SupercuspidalWindowSchurOrthogonalityStatement`
and `SupercuspidalCoefficientEllipticOrbitalStatement`, each taken once for the extension
`E : Type v` with representation spaces in `Type uW` and once for the base field `F : Type u`
over itself with representation spaces in `Type uV`. -/
def SupercuspidalCoefficientEllipticMatchingReductionStatement.{u, v, uV, uW} : Prop :=
  SupercuspidalWindowCoefficientCuspFormStatement.{u, v, uW} →
  SupercuspidalWindowCoefficientCuspFormStatement.{u, u, uV} →
  SupercuspidalWindowSchurOrthogonalityStatement.{u, v, uW} →
  SupercuspidalWindowSchurOrthogonalityStatement.{u, u, uV} →
  SupercuspidalCoefficientEllipticOrbitalStatement.{u, v, uW} →
  SupercuspidalCoefficientEllipticOrbitalStatement.{u, u, uV} →
  SupercuspidalCoefficientEllipticMatchingStatement.{u, v, uV, uW}

end Langlands.BaseChange
