import Langlands.Geometry.Building.Kottwitz.ChamberStatement
import Langlands.Geometry.Building.Kottwitz.RationalSurjectivityReduction
import Langlands.Geometry.Building.SpecialTorusExistenceProof
import Langlands.Geometry.Building.UnramifiedTwistedChamberProof
import Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelProof
import Langlands.GroupScheme.IntegralModel.UnramifiedSmoothDescentProof
import Langlands.Geometry.Building.Kottwitz.UnramifiedChamberExactSequenceProof
import Langlands.Geometry.Building.Kottwitz.ZExtensionKernelProof
import Langlands.Geometry.Building.Kottwitz.ZeroKernelProof

/-! # KP Corollary 11.7.5: rational surjectivity and the chamber quotient, proof -/

universe u

namespace Langlands.Geometry.Building.Kottwitz

/-- **KP Corollary 11.7.5.** For every connected reductive group over a nonarchimedean local
field, the rational Kottwitz homomorphism is surjective, and for every Galois-stable chamber of
supplied building data over the maximal unramified extension it induces an isomorphism
`G(F)_C / G(F)^0_C ≃ π₁(G)_I^Γ`. -/
theorem chamber : ChamberStatement.{u} :=
  chamberStatement_of_remainingInputs specialTorusExistence unramifiedTwistedChamber
    Langlands.BruhatTits.IntegralModels.unramifiedParahoricModel
    Langlands.GroupScheme.IntegralModel.unramifiedSmoothModelDescent
    unramifiedChamberExactSequence reductiveKottwitzDescent_assembled zeroKernel

end Langlands.Geometry.Building.Kottwitz
