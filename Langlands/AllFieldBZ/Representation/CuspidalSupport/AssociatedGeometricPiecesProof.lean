import Langlands.AllFieldBZ.Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.MinimalWeylTransportProof
import Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedGeometricPieceEquivalenceTheorem AssociatedGeometricPieceVanishingTheorem AssociatedJacquetFiltrationTheorem MinimalWeylTransportQuasicuspidalTheorem NonassociatedJacquetSubquotientsTheorem PadicAssociatedGeometricPiecesTheorem associatedGeometricPieceEquivalence associatedGeometricPieceVanishing fullRefinedInductionEquiv fullRefinedJacquetEquiv geometricPieceFunctor_subsingleton_of_proper_source minimalWeylTransportQuasicuspidal nonassociatedJacquetSubquotients_rankZero normalizedRefinedInductionFunctor_subsingleton padicAssociatedGeometricPieces refinedHalfModulus_eq_one_of_full refinedInverseHalfModulus_eq_one_of_full refinedModulus_eq_one_of_full
universe uF uV

/-- BZ77 2.13(c) individual-piece reduction: for every prime, `p`-adic field,
compatible topology and positive rank, nonconjugating pieces vanish,
conjugating pieces are whole-Levi transports, and minimal transport preserves
quasicuspidality. -/
theorem padicAssociatedGeometricPieces :
    PadicAssociatedGeometricPiecesTheorem.{uF, uV} :=
  fun F T n _ =>
    ⟨associatedGeometricPieceVanishing F T n,
      associatedGeometricPieceEquivalence F T n,
      minimalWeylTransportQuasicuspidal F T n⟩

end Langlands.AllFieldBZ.CuspidalSupport
