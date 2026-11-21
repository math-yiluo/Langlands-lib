import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerDistinctnessReduction
import Langlands.Automorphic.CuspidalArithmeticSpectralTransportProof

/-! # Distinct Mackey components from totally complex B6 -/

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

/-- Distinctness at the auxiliary place with the totally complex forms of B6 and prime cyclic
isobaric base change, under Harris's exact-stabilizer condition. -/
theorem proposition48ExactStabilizerDistinctnessTC :
    Proposition48ExactStabilizerDistinctnessTCStatement.{uF, uV} :=
  proposition48ExactStabilizerDistinctnessTCReduction
    Langlands.Automorphic.cuspidalArithmeticSpectralTransport.{0, 0, uV}

end Langlands.Global.Harris
