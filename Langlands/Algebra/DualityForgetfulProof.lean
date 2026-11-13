import Langlands.Algebra.DualityForgetfulInductionStatements
import Langlands.Algebra.NonUnitalTensorDuality
import Langlands.Algebra.RenardRegularCoefficientAdapters

/-! # Duality intertwines F with pseudo-F (Renard I.4.2) -/

set_option autoImplicit false

namespace Langlands.Algebra

universe uA uB v

/-- Renard I.4.2, Theorem, first natural isomorphism. -/
theorem dualityForgetful : DualityForgetfulStatement.{uA, uB, v} := by
  intro A B _ _ _ _ _ _ _ _ _ _ hA hB hLeft
  let : NonUnitalModule Bᵐᵒᵖ B := NonUnitalModule.rightRegular B
  intro hAB
  exact ⟨NonUnitalTensorDuality.naturalIso (S := A) (R := B) (X := B)
    hA hB hAB hLeft (NondegenerateTensorFunctor.rightRegular_isNondegenerate hB)
    (RenardRegularCoefficientAdapters.fInputCompatible ℂ hB)⟩

end Langlands.Algebra
