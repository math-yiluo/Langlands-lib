import Langlands.Global.AdelicEisensteinRegularAutomorphyStatement
import Langlands.Global.AdelicParameterTwistAutomorphyStatement

/-! # Automorphy of convergent Eisenstein series from automorphy of the twists

The automorphy of convergent Eisenstein series for a standard family
(`EisensteinRegularAutomorphyStatement`, Bernstein–Lapid Theorem 2.3 (1) in the region of
absolute convergence) follows from the automorphy of the twists `φ_λ` on the parabolic quotient
(`ParameterTwistAutomorphyStatement`, Bernstein–Lapid §2.2). -/

universe u

set_option autoImplicit false

namespace Langlands.Global

/-- `ParameterTwistAutomorphyStatement` implies `EisensteinRegularAutomorphyStatement`: if the
twists `φ_λ` of automorphic forms on a standard parabolic quotient are automorphic there, then
the convergent Eisenstein series `E(φ, λ)` are automorphic on `G(F) \ G(𝔸)`. -/
def EisensteinRegularAutomorphyReductionStatement : Prop :=
  ParameterTwistAutomorphyStatement.{u} → EisensteinRegularAutomorphyStatement.{u}

end Langlands.Global
