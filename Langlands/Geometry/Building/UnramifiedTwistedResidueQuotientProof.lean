import Langlands.Geometry.Building.UnramifiedTwistedResidueQuotientReduction
import Langlands.BruhatTits.IntegralModels.UnramifiedTwistedReductiveQuotientDescent
import Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsRadicalRootGenerationProof
import Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelConstruction
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriConnectedImageProof
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusBoundedModelProof
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusConnectedBoundAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralSurjectivityAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralFiniteGenerationProof
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNormPresentationProof
import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof
import Langlands.GroupScheme.IntegralModel.ConnectedGenerationProof
import Langlands.GroupScheme.Torus.QuotientRationalSurjectivityProof
import Langlands.GroupScheme.Torus.SurjectionIsogenySectionProof

/-! # Proof of the residue quotient at a twisted-fixed point for a Frobenius lift -/

universe u

open Langlands.GroupScheme Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

/-- The residue quotient at a twisted-fixed point for a Frobenius lift. The published
reduction `unramifiedTwistedResidueQuotientInputsReduction` is applied to proofs of its three
inputs. The parahoric model input is assembled from the published torus proofs through
`unramifiedParahoricModel_of_torusInputs`. -/
theorem unramifiedTwistedResidueQuotient : UnramifiedTwistedResidueQuotientStatement.{u} := by
  have hLift : UnramifiedTorusNeutralSurjectivityStatement.{u} :=
    unramifiedTorusNeutralSurjectivityAssembly connectedGeneration
      torusQuotientRationalSurjectivity unramifiedTorusNeutralFiniteGeneration
      torusSurjectionIsogenySection
  have hBound : UnramifiedTorusConnectedBoundStatement.{u} :=
    unramifiedTorusConnectedBoundAssembly unramifiedTorusBoundedModel hLift
      unramifiedTorusNormPresentation
  have hModel : UnramifiedTorusIwahoriModelStatement.{u} :=
    unramifiedTorusIwahoriModelAssembly IntegralModel.smoothHomExtension
      unramifiedTorusBoundedModel hBound unramifiedTorusIwahoriConnectedImage
  exact unramifiedTwistedResidueQuotientInputsReduction
    (unramifiedParahoricModel_of_torusInputs hModel hBound)
    unramifiedUpstairsRadicalRootGeneration unramifiedTwistedReductiveQuotientDescent

end Langlands.Geometry.Building
