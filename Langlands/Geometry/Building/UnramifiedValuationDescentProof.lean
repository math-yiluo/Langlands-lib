import Langlands.Geometry.Building.UnramifiedValuationDescentReduction
import Langlands.Geometry.Building.UnramifiedGaloisFixedApartmentProof
import Langlands.Geometry.Building.UnramifiedFixedCentralizerReduction
import Langlands.Geometry.Building.UnramifiedFixedOppositeProof
import Langlands.Geometry.Building.UnramifiedFixedLeviTransportReduction
import Langlands.Geometry.Building.UnramifiedLeviSharpApartmentTransportProof
import Langlands.Geometry.Building.UnramifiedTorusUnitFixedApartmentReduction
import Langlands.Geometry.Building.UnramifiedFixedPointTransporterReduction
import Langlands.Geometry.Building.UnramifiedFixedPairSpecialApartmentProof
import Langlands.Geometry.Building.UnramifiedTwistedFixedTranslationProof
import Langlands.Geometry.Building.UnramifiedSplitTranslationFixerProof

/-! # Descent of the valuation of the root datum from the maximal unramified extension

Kaletha–Prasad, Construction 9.6.1, Lemma 9.6.3 and Theorem 9.6.5 (with §9.6.6). -/

universe u

namespace Langlands.Geometry.Building

/-- **Descent of the valuation of the root datum from `K = F^ur` to `F`** (Kaletha–Prasad,
Construction 9.6.1, Lemma 9.6.3, Theorem 9.6.5 and §9.6.6). The proof composes published
results. The reduction `unramifiedValuationDescent_of_fixedLocus` takes four inputs: Galois-fixed
points exist in stable apartments, Levi transport holds at fixed points, V 6 on `Z_G(S)(F)` holds
at fixed points, and V 5 holds at fixed points. Each input is supplied by a published proof or
reduction. -/
theorem unramifiedValuationDescent : UnramifiedValuationDescentStatement.{u} :=
  have hLevi : UnramifiedFixedLeviTransportStatement.{u} :=
    unramifiedFixedLeviTransport_of_fixedApartment_and_leviSharp
      (unramifiedTorusUnitFixedApartmentReduction
        (unramifiedFixedPointTransporter_of_fixedPairSpecialApartment
          unramifiedFixedPairSpecialApartment)
        unramifiedTwistedFixedTranslation
        unramifiedSplitTranslationFixer)
      unramifiedLeviSharpApartmentTransport
  unramifiedValuationDescent_of_fixedLocus unramifiedGaloisFixedApartment hLevi
    (unramifiedFixedCentralizerCompatibility_of_leviTransport hLevi) unramifiedFixedOpposite

end Langlands.Geometry.Building
