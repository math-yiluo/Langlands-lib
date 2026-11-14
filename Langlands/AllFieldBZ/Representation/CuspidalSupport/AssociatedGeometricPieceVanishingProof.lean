import Langlands.AllFieldBZ.Representation.CuspidalSupport.AssociatedGeometricPiecesStatement
import Langlands.AllFieldBZ.Representation.CuspidalSupport.JacquetVanishingHelpers
import Langlands.Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedGeometricPieceEquivalenceTheorem AssociatedGeometricPieceVanishingTheorem AssociatedJacquetFiltrationTheorem MinimalWeylTransportQuasicuspidalTheorem NonassociatedJacquetSubquotientsTheorem PadicAssociatedGeometricPiecesTheorem associatedGeometricPieceVanishing geometricPieceFunctor_subsingleton_of_proper_source nonassociatedJacquetSubquotients_rankZero normalizedRefinedInductionFunctor_subsingleton
open Langlands.GeneralLinear
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem geometricPieceFunctor jacquetInductionFunctor
open Langlands.AllFieldBZ.Geometric
open scoped Pointwise
universe uF uV

/-- The published vanishing component, for every rank including zero. -/
theorem associatedGeometricPieceVanishing
    (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ) :
    AssociatedGeometricPieceVanishingTheorem.{uF, uV} F T n := by
  let := T.topology
  intro B C ρ hρ hBC w S R hS hR hw
  exact geometricPieceFunctor_subsingleton_of_proper_source F T B C w.val S R
    hS.2.1 hR.2.1 ρ hρ
    (source_refinement_proper_of_associated_nonconjugating B C hBC w.val S hS hw)

end Langlands.AllFieldBZ.CuspidalSupport
