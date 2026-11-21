import Langlands.Global.RankinSelberg.CuspidalLocalGKTransposePairingReduction
import Langlands.Representation.Archimedean.TransposePairingProof

/-! # The dual cusp forms lie in a cuspidal contragredient -/

universe u

namespace Langlands.Global.RankinSelbergGlobal

/-- The actual cuspidal inverse-transpose realization is a contragredient
and contains the prescribed dual cusp form of every original vector. -/
theorem cuspidalTransposeInverseContragredient :
    CuspidalTransposeInverseContragredientStatement.{u} :=
  cuspidalLocalGKTransposePairingReduction.{u} Archimedean.archimedeanTransposePairing.{u}

end Langlands.Global.RankinSelbergGlobal
