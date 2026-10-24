import Langlands.ClassField.Global.IntegralIdeleCoefficients

/-! # Finiteness of the quotient by integral idele classes -/

universe u

namespace Langlands.ClassField.Global

/-- The actual idele class group modulo the image of the integral ideles is finite. -/
def IntegralIdeleClassQuotientFinite : Prop :=
  ∀ (E : Type u) [Field E] [NumberField E],
    Finite (IntegralIdeleClassQuotient E)

end Langlands.ClassField.Global
