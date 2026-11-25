import Langlands.Geometry.Building.Kottwitz.ZeroKernelStatement
import Langlands.Geometry.Building.Kottwitz.UnramifiedZeroKernelProof
import Langlands.Geometry.Building.UnramifiedZeroDescentProof

/-! # KP Proposition 11.5.4: the zero subgroup, proof -/

universe u

namespace Langlands.Geometry.Building.Kottwitz

/-- **KP Proposition 11.5.4.** For every connected reductive group over a nonarchimedean local
field and every datum defining the zero subgroup `G(F)^0`, `G(F)^0` is the kernel of the
rational Kottwitz homomorphism. -/
theorem zeroKernel : ZeroKernelStatement.{u} :=
  zeroKernel_of_unramifiedZeroDescent unramifiedZeroDescent

end Langlands.Geometry.Building.Kottwitz
