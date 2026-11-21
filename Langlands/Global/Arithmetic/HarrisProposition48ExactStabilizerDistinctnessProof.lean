import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerDistinctnessReduction
import Langlands.Automorphic.CuspidalArithmeticSpectralTransportProof

/-! # Distinct Mackey components at the auxiliary place from B6 -/

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

/-- From B6 and prime cyclic isobaric base change, Mackey constituents from distinct
 double cosets have non-isomorphic components above the auxiliary place under the
 exact-stabilizer condition. -/
theorem proposition48ExactStabilizerDistinctness :
    Proposition48ExactStabilizerDistinctnessStatement.{uF, uV} :=
  proposition48ExactStabilizerDistinctnessReduction
    Langlands.Automorphic.cuspidalArithmeticSpectralTransport.{0, 0, uV}

end Langlands.Global.Harris
