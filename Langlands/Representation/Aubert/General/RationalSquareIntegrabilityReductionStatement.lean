import Langlands.Representation.Aubert.General.RationalSquareIntegrabilityStatement
import Langlands.BruhatTits.SpecialCompact.JointBasisStatement

/-! # Reduction of strict Jacquet square integrability to joint geometry -/

namespace Langlands.Aubert.General.RationalPointFamily

/-- The joint actual special-compact and simultaneous-basis existence theorem
suffices for the complete strict normalized Jacquet square-integrability criterion. -/
def RationalStrictJacquetSquareIntegrabilityReductionStatement.{u, v} : Prop :=
  BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u} →
    RationalStrictJacquetSquareIntegrabilityStatement.{u, v}

end Langlands.Aubert.General.RationalPointFamily
