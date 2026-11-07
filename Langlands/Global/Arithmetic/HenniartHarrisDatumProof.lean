import Langlands.Global.Arithmetic.HenniartHarrisDatumReductionProof
import Langlands.Global.Arithmetic.CMHalfWeightCharacterProof

/-! # Henniart's Harris datum and the datum characters -/

universe uF uE uE' uL

namespace Langlands.Global

/-- The datum characters exist on every paired-place configuration. -/
theorem harrisDatumCharacterRealization :
    HarrisDatumCharacterRealizationStatement.{uF, uE, uE', uL} :=
  harrisDatumCharacterRealizationOfHalfWeight cmHalfWeightCharacter

/-- The exact target `HenniartHarrisDatumStatement`: one CM field and place serve every
intermediate field, with the data of Harris's Proposition 4.8 for every character. -/
theorem henniartHarrisDatum : HenniartHarrisDatumStatement.{uF} :=
  henniartHarrisDatumOfHalfWeight cmHalfWeightCharacter

end Langlands.Global
