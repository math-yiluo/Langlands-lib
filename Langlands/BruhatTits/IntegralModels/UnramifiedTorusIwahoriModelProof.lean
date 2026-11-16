import Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusBoundedModelProof
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusConnectedBoundAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralSurjectivityProof
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNormPresentationProof
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriConnectedImageProof
import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof

/-!
# Connected models of torus Iwahori subgroups over the maximal unramified integers

The published reduction `unramifiedTorusIwahoriModelAssembly`, applied to the
published proofs of its four inputs. The connected-bound input is obtained from
the published reduction `unramifiedTorusConnectedBoundAssembly` and the
published proofs of its three premises.
-/

universe u

namespace Langlands.BruhatTits.IntegralModels

/-- **Connected torus Iwahori models** (KP Proposition B.8.4(3) with Corollary B.8.7, over
the maximal unramified field): for a torus `T` over `K = inertiaFixedField F` split by a
finite Galois `L`, there is a smooth model of `T` over `O = fixedFieldIntegers F` with
geometrically connected fibres whose integral points are exactly the norm-defined
Iwahori subgroup `T(K)⁰`. -/
theorem unramifiedTorusIwahoriModel : UnramifiedTorusIwahoriModelStatement.{u} :=
  unramifiedTorusIwahoriModelAssembly.{u} Langlands.GroupScheme.IntegralModel.smoothHomExtension
    unramifiedTorusBoundedModel
    (unramifiedTorusConnectedBoundAssembly.{u} unramifiedTorusBoundedModel
      unramifiedTorusNeutralSurjectivity unramifiedTorusNormPresentation)
    unramifiedTorusIwahoriConnectedImage

end Langlands.BruhatTits.IntegralModels
