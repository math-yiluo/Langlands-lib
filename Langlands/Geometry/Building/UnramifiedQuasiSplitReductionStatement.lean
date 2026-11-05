import Langlands.Geometry.Building.UnramifiedQuasiSplitStatement
import Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitStatement

/-! # The actual unramified specialization of Henselian quasi-splitness -/

universe u

namespace Langlands.Geometry.Building

/-- The generic Henselian discrete-field theorem applies to the published
maximal unramified extension of every nonarchimedean local field. -/
def UnramifiedQuasiSplitReductionStatement : Prop :=
  Langlands.GroupScheme.HenselianDiscreteQuasiSplitStatement.{u} →
    UnramifiedQuasiSplitStatement.{u}

end Langlands.Geometry.Building
