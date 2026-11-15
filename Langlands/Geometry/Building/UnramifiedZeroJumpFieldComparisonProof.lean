import Langlands.Geometry.Building.UnramifiedZeroJumpFieldComparisonAssembly
import Langlands.Geometry.Building.UnramifiedZeroJumpDescentProof
import Langlands.Geometry.Building.UnramifiedZeroJumpForwardDescent

/-! # The zero-jump comparison over `F` and `F^ur`

Proof of `Langlands.Geometry.Building.UnramifiedZeroJumpFieldComparisonStatement`: the assembly
`unramifiedZeroJumpFieldComparison_of_galoisDescent` applied to the ascent principle
`MaximalUnramified.unramifiedZeroJump_forwardDescent` and the descent principle
`unramifiedZeroJumpGaloisDescent`. -/

universe u

namespace Langlands.Geometry.Building

/-- **The zero-jump comparison over `F` and `F^ur`.** -/
theorem unramifiedZeroJumpFieldComparison : UnramifiedZeroJumpFieldComparisonStatement.{u} :=
  unramifiedZeroJumpFieldComparison_of_galoisDescent
    MaximalUnramified.unramifiedZeroJump_forwardDescent unramifiedZeroJumpGaloisDescent

end Langlands.Geometry.Building
