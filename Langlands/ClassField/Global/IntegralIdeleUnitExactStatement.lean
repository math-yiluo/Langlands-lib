import Langlands.ClassField.Global.IntegralIdeleCoefficients

/-! # Exactness of the ordinary-unit sequence in integral ideles -/

universe u

namespace Langlands.ClassField.Global

/-- Ordinary units inject into integral ideles and are precisely the kernel of their
map to integral idele classes. -/
def IntegralIdeleUnitSequenceExact : Prop :=
  ∀ (E : Type u) [Field E] [NumberField E],
    Function.Injective (ringIntegerUnitsToIntegralIdeles E) ∧
      (integralIdelesToClasses E).ker = (ringIntegerUnitsToIntegralIdeles E).range

end Langlands.ClassField.Global
