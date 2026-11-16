import Langlands.GroupScheme.SimplyConnected.LocalUnramifiedIwahoriModelAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelProof
import Langlands.GroupScheme.IntegralModel.UnramifiedSmoothDescentProof
import Langlands.Geometry.Building.UnramifiedSimplyConnectedChamberStabilizerProof

/-! # The Iwahori model of a Galois-stable chamber of a simply connected group -/

universe u

open AlgebraicGeometry
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building
open Langlands.BruhatTits.IntegralModels

namespace Langlands.GroupScheme

/-- A Galois-stable chamber over the maximal unramified extension has a smooth
model over the original integers with connected special fibre and with the
full chamber stabilizer as its unramified integral-point image. -/
theorem localSimplyConnectedUnramifiedIwahoriModel :
    LocalSimplyConnectedUnramifiedIwahoriModelStatement.{u} := by
  apply localSimplyConnectedUnramifiedIwahoriModel_of_inputs
    unramifiedParahoricModel IntegralModel.unramifiedSmoothModelDescent
  intro F _ _ _ _ G _ hG C Y hY g hgy
  exact MaximalUnramified.simplyConnectedChamberStabilizer
    F (baseChanged F (inertiaFixedField F) G)
    (isSimplyConnectedFieldExtension F (inertiaFixedField F) G hG) C Y hY g hgy

end Langlands.GroupScheme
