import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralSurjectivityAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralFiniteGenerationProof
import Langlands.GroupScheme.IntegralModel.ConnectedGenerationProof
import Langlands.GroupScheme.Torus.QuotientRationalSurjectivityProof
import Langlands.GroupScheme.Torus.SurjectionIsogenySectionProof

/-!
# Neutral integral-point lifting for unramified-field tori (KP B.8.6)

The published reduction `unramifiedTorusNeutralSurjectivityAssembly`, applied
to the published proofs of its four premises.
-/

universe u

namespace Langlands.BruhatTits.IntegralModels

open Langlands.GroupScheme

/-- **KP Corollary B.8.6** over the maximal unramified field: for a
scheme-surjective homomorphism `q : B → C` of tori with torus kernel, every
neutral integral point of `C` lifts to a neutral integral point of `B`. -/
theorem unramifiedTorusNeutralSurjectivity :
    UnramifiedTorusNeutralSurjectivityStatement.{u} :=
  unramifiedTorusNeutralSurjectivityAssembly connectedGeneration
    torusQuotientRationalSurjectivity unramifiedTorusNeutralFiniteGeneration
    torusSurjectionIsogenySection

end Langlands.BruhatTits.IntegralModels
