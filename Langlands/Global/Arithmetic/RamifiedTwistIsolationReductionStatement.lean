import Langlands.Global.Arithmetic.CharacterPrescriptionStatement

/-!
# Ramified twist isolation from global prescription and local existence

This proposition retains both arithmetic existence assertions as premises.
It uses the existing characters, component maps, and principal-unit predicate.
-/

universe u

namespace Langlands.Global

/-- Global finite-order prescription and arbitrarily ramified finite-order local
characters suffice for simultaneous ramified twist isolation. -/
def RamifiedTwistIsolationOfInputsStatement : Prop :=
  FiniteOrderCharacterPrescriptionStatement.{u} →
  LocalCharactersArbitrarilyRamifiedStatement.{u} →
  RamifiedTwistIsolationStatement.{u}

end Langlands.Global
