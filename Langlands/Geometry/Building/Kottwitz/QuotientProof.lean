import Langlands.Geometry.Building.Kottwitz.QuotientStatement
import Langlands.Geometry.Building.Kottwitz.QuotientReduction
import Langlands.Geometry.Building.Kottwitz.ZeroKernelProof
import Langlands.Geometry.Building.Kottwitz.CharacterKernelProof
import Langlands.Geometry.Building.Kottwitz.ChamberProof

/-! # KP Corollary 11.7.6: the three rational Kottwitz quotients, proof -/

universe u

namespace Langlands.Geometry.Building.Kottwitz

/-- **KP Corollary 11.7.6.** For every connected reductive group over a nonarchimedean local
field, the Kottwitz homomorphism induces isomorphisms `G(F)/G(F)^0 ≃ π₁(G)_I^Γ`,
`G(F)^1/G(F)^0 ≃ (π₁(G)_I^Γ)_tor` and `G(F)/G(F)^1 ≃ π₁(G)_I^Γ / (π₁(G)_I^Γ)_tor`. -/
theorem quotient : QuotientStatement.{u} :=
  quotientStatement_of_chamberStatement zeroKernel characterKernel chamber

end Langlands.Geometry.Building.Kottwitz
