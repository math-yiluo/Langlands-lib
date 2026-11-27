import Langlands.Automorphic.GroupSchemeAutomorphicFunctionUniformGrowthStatement
import Langlands.Global.AdelicIntertwiningAutomorphyStatement

/-! # Smooth slices of intertwining integrals from uniform growth

The implication `AutomorphicFunctionUniformGrowthStatement → IntertwiningSmoothSlicesStatement`:
if automorphic functions on `Γ \ G(𝔸)` have uniformly moderate growth for every subgroup `Γ` of the
adelic points, then the regular intertwining integrals have smooth infinite slices (the smoothness
part of Mœglin–Waldspurger II.1.6 (i)). A proof instantiates the premise at the parabolic quotient
`U(𝔸) M(F) \ G(𝔸)`. -/

universe u

set_option autoImplicit false

namespace Langlands.Global

open Langlands.Automorphic.GroupSchemeFunctions

/-- Smoothness of regular intertwining integrals in the infinite variable follows from uniformly
moderate growth of automorphic functions on `Γ \ G(𝔸)`. -/
def IntertwiningSmoothSlicesReductionStatement : Prop :=
  AutomorphicFunctionUniformGrowthStatement.{u} → IntertwiningSmoothSlicesStatement.{u}

end Langlands.Global
