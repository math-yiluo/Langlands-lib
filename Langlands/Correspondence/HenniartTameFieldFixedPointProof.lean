import Langlands.Correspondence.HenniartTameFieldCount
import Langlands.Correspondence.HenniartTameWeilFieldsProof

/-!
# The fixed-point formula over the tame fields: proof
-/

namespace Langlands.Henniart

universe uK uW

/-- **Fixed-point formula**, `WeilTameFieldFixedPointStatement`: for `p ∤ m`, `φ` of degree one,
a Frobenius coset datum `D` and `g` in inertia, the field `E` indexed by the coset of `g` has
`C_E(p^r, j)` equal to `q_K - 1` times the number of tame wild classes for `D.kernel` fixed by
conjugation by `g φ`. -/
theorem weilTameFieldFixedPoint : WeilTameFieldFixedPointStatement.{uK, uW} :=
  weilTameFieldFixedPoint_of_parametrization tameWeilFrobeniusParametrization.{uK}

end Langlands.Henniart
