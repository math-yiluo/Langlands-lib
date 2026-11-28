import Langlands.TraceFormula.ArchimedeanUnitaryCharacterSeparationStatement

/-! # Character separation from trace class of smooth integrated operators -/

universe uF uι uH uE

namespace Langlands.TraceFormula

/-- Trace class of the smooth integrated operators, in the summand and target Hilbert
universes, suffices for separation of the stated summable unitary character families. -/
def ArchimedeanUnitaryCharacterSeparationReductionStatement : Prop :=
  ArchimedeanUnitaryTraceClassStatement.{uF, uH} →
    ArchimedeanUnitaryTraceClassStatement.{uF, uE} →
      ArchimedeanUnitaryCharacterSeparationStatement.{uF, uι, uH, uE}

end Langlands.TraceFormula
