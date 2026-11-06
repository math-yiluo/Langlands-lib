import Langlands.Global.Arithmetic.HenniartHarrisDatumStatement
import Langlands.Global.Arithmetic.CMHalfWeightCharacterStatement

/-!
# Reductions of the Harris datum targets to the weight-one CM characters

Implications from `CMHalfWeightCharacterStatement` to the character realization and to
Henniart's Harris datum. Their existence inputs stay explicit; nothing is proved here.
-/

universe uF uE uE' uL

namespace Langlands.Global

/-- The character realization on every paired-place configuration follows from the existence
of conjugate-inverse weight-one Hecke characters on CM fields in the universe of `E'`. -/
def HarrisDatumCharacterRealizationOfHalfWeightStatement : Prop :=
  CMHalfWeightCharacterStatement.{uE'} →
    HarrisDatumCharacterRealizationStatement.{uF, uE, uE', uL}

/-- Henniart's Harris datum over a common base follows from the existence of
conjugate-inverse weight-one Hecke characters on CM fields in `Type`. -/
def HenniartHarrisDatumOfHalfWeightStatement : Prop :=
  CMHalfWeightCharacterStatement.{0} → HenniartHarrisDatumStatement.{uF}

end Langlands.Global
