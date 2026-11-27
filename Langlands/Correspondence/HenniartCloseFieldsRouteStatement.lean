import Langlands.Correspondence.HenniartCloseFieldsStatement
import Langlands.LocalFactor.Ramification.CloseFieldsStatement

/-! # From the close-fields Galois quotients to Weil orbit counts -/

namespace Langlands.Henniart

/-- The filtered absolute Galois quotient comparison implies the equality of
torsion-number-one Weil orbit counts in the strict slope range of E1a. -/
def CloseFieldsTwistCountFromGaloisQuotientStatement.{u, uW} : Prop :=
  Langlands.Ramification.Local.CloseFieldsGaloisQuotientStatement.{u} →
    CloseFieldsTwistCountStatement.{u, uW}

end Langlands.Henniart
