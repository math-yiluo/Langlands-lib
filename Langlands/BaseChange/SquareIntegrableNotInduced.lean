import Langlands.BaseChange.PadicSquareIntegrableNotInduced
import Langlands.BaseChange.SquareIntegrableNotInducedStatement
import Langlands.LocalField.CharZeroPadicRealization

/-! # Square-integrable non-induction on the given characteristic-zero local field -/

namespace Langlands.BaseChange

open CharZeroLocalField

universe u uV

/-- Irreducible square-integrable representations of `GL_n(F)` over a characteristic-zero
local field are not isomorphic to smooth inductions from proper standard block parabolics. -/
theorem squareIntegrableNotInduced : SquareIntegrableNotInducedStatement.{u, uV} := by
  intro F _ _ _ _ _ n V _ _ π hirr hsq B hB X _ _ Ξ hΞ
  exact (topologicalData F).isEmpty_equiv_smoothInduced_of_squareIntegrable B π hirr hsq hB Ξ hΞ

end Langlands.BaseChange
