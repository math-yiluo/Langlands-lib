import Langlands.AllFieldBZ.Representation.CuspidalSupport.AssociatedConditional
import Langlands.AllFieldBZ.Representation.CuspidalSupport.AssociatedGeometricPiecesProof
import Langlands.AllFieldBZ.Representation.Geometric.GeometricLemmaProof
import Langlands.Representation.CuspidalSupport.AssociatedProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.AssociatedProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.AssociatedProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedGeometricPieceEquivalenceTheorem AssociatedGeometricPieceVanishingTheorem AssociatedJacquetFiltrationTheorem MinimalNonzeroJacquetTheorem MinimalWeylTransportQuasicuspidalTheorem NonassociatedJacquetSubquotientsTheorem PadicAssociatedGeometricPiecesTheorem TotalConjugatingCountTheorem associatedFiltration_of_geometricPieces associatedGeometricPieceEquivalence associatedGeometricPieceVanishing associatedJacquetFiltration associatedJacquetFiltration_of_geometricPieces associatedJacquetFiltration_of_prerequisites associatedJacquetFiltration_rankZero fullRefinedInductionEquiv fullRefinedJacquetEquiv geometricPieceFunctor_subsingleton_of_proper_source minimalNonzeroJacquet minimalWeylTransportQuasicuspidal nonassociatedJacquetSubquotients_rankZero normalizedRefinedInductionFunctor_subsingleton padicAssociatedGeometricPieces rankZero_jacquetInductionEquiv refinedHalfModulus_eq_one_of_full refinedInverseHalfModulus_eq_one_of_full refinedModulus_eq_one_of_full totalConjugatingCount
universe uF uV

/-- The actual normalized Jacquet module of quasicuspidal induction between
associated Levis is quasicuspidal and has one transport factor for every
minimal conjugating permutation, in every rank. -/
theorem associatedJacquetFiltration
    (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ) :
    AssociatedJacquetFiltrationTheorem.{uF, uV} F T n :=
  associatedJacquetFiltration_of_prerequisites F T n
    Geometric.padicGeometricLemma
    padicAssociatedGeometricPieces
    ObjectRepFiltration.zeroFactorDeletionTheorem

end Langlands.AllFieldBZ.CuspidalSupport
