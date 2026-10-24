import Langlands.Representation.Whittaker.InducedLocalizationStatement

/-! # Algebraic reduction of induced Whittaker type to localized heredity -/

namespace Langlands

universe uF uV

/-- The full character-quotient comparison implies the unchanged functional-space iff. -/
def InducedWhittakerTypeReductionStatement : Prop :=
  InducedLocalizationStatement.{uF, uV} → InducedWhittakerTypeStatement.{uF, uV}

end Langlands
