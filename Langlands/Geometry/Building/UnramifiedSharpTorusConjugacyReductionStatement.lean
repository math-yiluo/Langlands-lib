import Langlands.Geometry.Building.UnramifiedSharpTorusConjugacyStatement
import Langlands.Geometry.Building.UnramifiedQuasiSplitStatement
import Langlands.GroupScheme.Rational.ConjugacyStatement
import Langlands.GroupScheme.Rational.SimplyConnectedCentralizerProductStatement
import Langlands.GroupScheme.Rational.QuasiSplitMaximalTorusCentralizerStatement

/-! # Conditional unramified sharp conjugacy: reduction statement -/

universe u

namespace Langlands.Geometry.Building

/-- The four structural assertions imply the exact unramified sharp-conjugacy
proposition. All four remain premises of this conditional reduction. -/
def UnramifiedSharpTorusConjugacyReductionStatement : Prop :=
  Langlands.GroupScheme.MaximalSplitTorusConjugacyStatement.{u} →
  Langlands.GroupScheme.SimplyConnectedCentralizerProductStatement.{u} →
  Langlands.GroupScheme.QuasiSplitMaximalTorusCentralizerStatement.{u} →
  UnramifiedQuasiSplitStatement.{u} →
  UnramifiedSharpTorusConjugacyStatement.{u}

end Langlands.Geometry.Building
