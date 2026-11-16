import Langlands.Geometry.Building.UnramifiedFixedOppositeReduction
import Langlands.Geometry.Building.UnramifiedFixedWallInvarianceReduction
import Langlands.Geometry.Building.UnramifiedFixedLeviTransportReduction
import Langlands.Geometry.Building.UnramifiedLeviSharpApartmentTransportProof
import Langlands.Geometry.Building.UnramifiedFixedDepthZeroOppositeProof
import Langlands.Geometry.Building.UnramifiedTorusUnitFixedApartmentReduction
import Langlands.Geometry.Building.UnramifiedFixedPointTransporterReduction
import Langlands.Geometry.Building.UnramifiedTwistedFixedTranslationProof
import Langlands.Geometry.Building.UnramifiedSplitTranslationFixerProof
import Langlands.Geometry.Building.UnramifiedFixedPairSpecialApartmentProof

/-! # V 5 at the Galois-fixed points of the unramified apartment (KP 9.4.9–9.4.10) -/

universe u

namespace Langlands.Geometry.Building

/-- Axiom V 5 for the restricted root-function family at every `Aut(K/F)`-fixed point of the
apartment of the maximal unramified extension (Kaletha–Prasad, Proposition 9.4.9 and
Corollary 9.4.10). The proof composes published reductions and proofs. -/
theorem unramifiedFixedOpposite : UnramifiedFixedOppositeStatement.{u} :=
  unramifiedFixedOpposite_of_wallInvariance
    (unramifiedFixedWallInvariance_of_depthZero_of_leviTransport
      unramifiedFixedDepthZeroOpposite
      (unramifiedFixedLeviTransport_of_fixedApartment_and_leviSharp
        (unramifiedTorusUnitFixedApartmentReduction
          (unramifiedFixedPointTransporter_of_fixedPairSpecialApartment
            unramifiedFixedPairSpecialApartment)
          unramifiedTwistedFixedTranslation
          unramifiedSplitTranslationFixer)
        unramifiedLeviSharpApartmentTransport))

end Langlands.Geometry.Building
