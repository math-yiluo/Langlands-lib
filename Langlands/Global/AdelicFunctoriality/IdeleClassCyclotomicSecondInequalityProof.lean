import Langlands.Global.AdelicFunctoriality.CyclotomicSecondInequalityReduction

/-! # Conditional cyclotomic reduction of the actual second inequality -/

universe u v

namespace Langlands.Global.AdelicFunctoriality

/-- The exact conditional reduction, using the published cyclotomic construction. -/
theorem ideleClassCyclotomicSecondInequalityReduction :
    IdeleClassCyclotomicSecondInequalityReduction.{u, v} :=
  ideleClassCyclotomicSecondInequalityReduction_holds.{u, v}

end Langlands.Global.AdelicFunctoriality
