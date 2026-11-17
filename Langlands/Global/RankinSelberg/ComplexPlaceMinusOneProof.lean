import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction
import Langlands.Global.RankinSelberg.ComplexPlaceMinusOneScalar

/-! # Proof of the minus-one premise at a complex place

`ComplexPlaceMinusOneStatement`: if an actual cuspidal realization `T` of `GL_(r+1)` has the
parameter `d` at the complex place `w`, then `complexMinusOneScalar T w = complexCentralSign d`.
This is `ComplexPlaceMinusOne.complexMinusOneScalar_eq_prod`, since `complexCentralSign d` is
by definition `∏_j χ_j(-1)`.
-/

universe u

namespace Langlands.Global.RankinSelbergGlobal

/-- **The minus-one premise.** If an actual cuspidal realization `T` of `GL_(r+1)` has the
parameter `d` at the complex place `w`, then `-1 ∈ U(r+1)` at `w` acts on `T` by
`complexCentralSign d = ∏_j χ_j(-1)`. -/
theorem complexPlaceMinusOne : ComplexPlaceMinusOneStatement.{u} :=
  fun _ _ _ _ _ T w d hd => ComplexPlaceMinusOne.complexMinusOneScalar_eq_prod T w d hd

end Langlands.Global.RankinSelbergGlobal
