import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleReduction
import Langlands.GroupScheme.Reductive.SpecialLinearTorusAutomorphismProof

/-! # The Galois-twisted special-linear presentation of type-A groups -/

universe u

namespace Langlands.GroupScheme

/-- The exact finite-Galois special-linear presentation, with discrepancy formulas
classified by the original Tits star action and the original split-torus weights. -/
theorem specialLinearTitsCocycle : SpecialLinearTitsCocycleStatement.{u} :=
  specialLinearTitsCocycle_of_torusAutomorphism
    SpecialLinearTorusAutomorphism.specialLinearTorusAutomorphism

end Langlands.GroupScheme
