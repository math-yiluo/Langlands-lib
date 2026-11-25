import Langlands.ClassFieldTheory.Global.CyclicIdeleClassHerbrandQuotientStatement

/-! # Reducing the idele-class Herbrand quotient to one field universe -/

namespace Langlands.ClassFieldTheory.Global

/-- The common-universe Herbrand assertion suffices for arbitrary independent
base-field and extension-field universes. This is only the reduction statement. -/
def CyclicIdeleClassHerbrandQuotientUniverseReduction.{u, v} : Prop :=
  CyclicIdeleClassHerbrandQuotient.{v, v} →
    CyclicIdeleClassHerbrandQuotient.{u, v}

end Langlands.ClassFieldTheory.Global
