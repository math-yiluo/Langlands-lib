import Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesProof
import Langlands.AllField.Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof
import Langlands.AllField.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof
import Langlands.AllField.Representation.CuspidalSupport.MinimalWeylTransportProof
/-! The individual-piece reduction of BZ77 2.13(c), assembled from its three
published components. -/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedGeometricPieceEquivalenceTheorem AssociatedGeometricPieceVanishingTheorem AssociatedJacquetFiltrationTheorem MinimalWeylTransportQuasicuspidalTheorem NonassociatedJacquetSubquotientsTheorem PadicAssociatedGeometricPiecesTheorem associatedGeometricPieceEquivalence associatedGeometricPieceVanishing fullRefinedInductionEquiv fullRefinedJacquetEquiv geometricPieceFunctor_subsingleton_of_proper_source minimalWeylTransportQuasicuspidal nonassociatedJacquetSubquotients_rankZero normalizedRefinedInductionFunctor_subsingleton padicAssociatedGeometricPieces refinedHalfModulus_eq_one_of_full refinedInverseHalfModulus_eq_one_of_full refinedModulus_eq_one_of_full
open Langlands.AllField.CuspidalSupport

universe uF uV

/-- BZ77 2.13(c) individual-piece reduction: for every prime, `p`-adic field,
compatible topology and positive rank, nonconjugating pieces vanish,
conjugating pieces are whole-Levi transports, and minimal transport preserves
quasicuspidality. -/
theorem padicAssociatedGeometricPieces :
    PadicAssociatedGeometricPiecesTheorem.{uF, uV} :=
  fun F _ T n _ =>
    ⟨associatedGeometricPieceVanishing F T n,
      associatedGeometricPieceEquivalence F T n,
      minimalWeylTransportQuasicuspidal F T n⟩

end Langlands.AllField.CuspidalSupport
