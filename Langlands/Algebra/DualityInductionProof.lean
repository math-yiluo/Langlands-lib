import Langlands.Algebra.DualityForgetfulInductionStatements
import Langlands.Algebra.NonUnitalTensorDuality
import Langlands.Algebra.RenardRegularCoefficientAdapters

/-! # Duality intertwines P with I (Renard I.4.2) -/

set_option autoImplicit false

namespace Langlands.Algebra

universe uA uB v

/-- Renard I.4.2, Theorem, second natural isomorphism. -/
theorem dualityInduction : DualityInductionStatement.{uA, uB, v} := by
  intro A B _ _ _ _ _ _ _ _ _ _ hA hB hRight
  let : NonUnitalModule B B := NonUnitalModule.regular B
  intro hBA
  exact ⟨NonUnitalTensorDuality.naturalIso (S := B) (R := A) (X := B)
    hB hA hBA (NondegenerateTensorFunctor.regular_isNondegenerate hB) hRight
    (RenardRegularCoefficientAdapters.pInputCompatible ℂ hA hRight)⟩

end Langlands.Algebra
