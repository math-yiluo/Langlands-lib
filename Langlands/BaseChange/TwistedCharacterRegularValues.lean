import Langlands.BaseChange.TwistedCharacterRegularValuesGeometry
import Langlands.BaseChange.SigmaLiftCharacterIdentity.LocalValues
import Langlands.HarmonicAnalysis.CompactSubmersionPushforward
import Langlands.JacquetLanglands.CharacterStatements

/-! # Twisted character regular values -/

namespace Langlands.BaseChange

universe u v uW

/-- The twisted character has a local value at each σ-regular element. -/
theorem twistedCharacterRegularValues : TwistedCharacterRegularValuesStatement.{u, v, uW} :=
  twistedCharacterRegularValues_of_compactSubmersion HarmonicAnalysis.compactSubmersionPushforward

/-- The degree-one case gives ordinary character values on the regular semisimple set. -/
theorem ordinaryRegularSemisimpleCharacterValues_charZero
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (n : ℕ) : JacquetLanglands.HasRegularSemisimpleCharacterValues.{u, uW} F n :=
  SigmaLiftCharacterIdentity.ordinary_regular_values F n twistedCharacterRegularValues.{u, u, uW}

end Langlands.BaseChange
