import Langlands.Algebra.RenardCommutativeEndomorphismDimensionProof

/-! Proof of the source-facing subalgebra form of Renard 2026, Appendix C.I. -/

namespace Langlands.Renard

universe uV

/-- Renard C.I for a subalgebra given together with an explicit generation equality. -/
theorem commutativeSubalgebraDimension :
    CommutativeSubalgebraDimensionStatement.{uV} := by
  intro V _ _ _ l a R hc hR
  subst hR
  exact commutativeEndomorphismDimension V l a hc

end Langlands.Renard
