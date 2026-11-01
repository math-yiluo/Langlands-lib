import Langlands.Algebra.NondegeneratePInductionLeftExactness
import Langlands.Algebra.NondegeneratePInductionRightExactness

/-!
# Exactness of the actual P and pseudo-F induction functors

The fixed regular-carrier kernel and cokernel arguments prove exactly the
published closed P/pseudo-F assertion of Renard I.2.4, at independent universes.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

universe uA uB v

/-- Left exactness of actual pseudo-F and right exactness of actual P. -/
theorem nondegeneratePInductionExactness :
    NondegeneratePInductionExactnessTheorem.{uA, uB, v} := by
  intro A B _ _ hA hB _ hBA hnd
  exact ⟨RenardHomFunctors.pseudoF_sequenceLeftExact.{uA, uB, v} hBA hA hB,
    NondegeneratePInductionRightExactness.sequenceRightExact.{uA, uB, v}
      hB hBA hnd hA⟩

end Langlands.Algebra
