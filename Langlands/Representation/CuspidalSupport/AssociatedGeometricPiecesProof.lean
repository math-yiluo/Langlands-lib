import Langlands.Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof
import Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof
import Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof

/-! The individual-piece reduction of BZ77 2.13(c), assembled from its three
published components. -/

namespace Langlands.CuspidalSupport

universe uF uV

/-- BZ77 2.13(c) individual-piece reduction: for every prime, `p`-adic field,
compatible topology and positive rank, nonconjugating pieces vanish,
conjugating pieces are whole-Levi transports, and minimal transport preserves
quasicuspidality. -/
theorem padicAssociatedGeometricPieces :
    PadicAssociatedGeometricPiecesTheorem.{uF, uV} :=
  fun _ _ F T n _ =>
    ⟨associatedGeometricPieceVanishing F T n,
      associatedGeometricPieceEquivalence F T n,
      minimalWeylTransportQuasicuspidal F T n⟩

end Langlands.CuspidalSupport
