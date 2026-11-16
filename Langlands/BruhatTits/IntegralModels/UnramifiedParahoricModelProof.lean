import Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelConstruction
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusBoundedModelProof
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusConnectedBoundAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriConnectedImageProof
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralFiniteGenerationProof
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralSurjectivityAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNormPresentationProof
import Langlands.GroupScheme.IntegralModel.ConnectedGenerationProof
import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof
import Langlands.GroupScheme.Torus.QuotientRationalSurjectivityProof
import Langlands.GroupScheme.Torus.SurjectionIsogenySectionProof

/-! # Proof of the unramified parahoric model statement -/

universe u

open Langlands.GroupScheme

namespace Langlands.BruhatTits.IntegralModels

set_option maxHeartbeats 1600000 in
/-- KP Theorems 8.3.2 and 8.3.13 over the maximal unramified integers:
compatible full and relative neutral models with both exact fixer identities. -/
theorem unramifiedParahoricModel : UnramifiedParahoricModelStatement.{u} := by
  have hLift : UnramifiedTorusNeutralSurjectivityStatement.{u} :=
    unramifiedTorusNeutralSurjectivityAssembly.{u} connectedGeneration.{u}
      torusQuotientRationalSurjectivity.{u} unramifiedTorusNeutralFiniteGeneration.{u}
      torusSurjectionIsogenySection.{u}
  have hBound : UnramifiedTorusConnectedBoundStatement.{u} :=
    unramifiedTorusConnectedBoundAssembly.{u} unramifiedTorusBoundedModel.{u}
      hLift unramifiedTorusNormPresentation.{u}
  have hModel : UnramifiedTorusIwahoriModelStatement.{u} :=
    unramifiedTorusIwahoriModelAssembly.{u} IntegralModel.smoothHomExtension.{u}
      unramifiedTorusBoundedModel.{u} hBound unramifiedTorusIwahoriConnectedImage.{u}
  exact unramifiedParahoricModel_of_torusInputs.{u} hModel hBound

end Langlands.BruhatTits.IntegralModels
