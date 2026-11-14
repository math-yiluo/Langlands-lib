import Langlands.Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof
import Langlands.AllField.Representation.CuspidalSupport.AssociatedGeometricPiecesStatement
import Langlands.AllField.Representation.CuspidalSupport.JacquetVanishingHelpers
/-! Vanishing of nonconjugating geometric pieces for associated Levis. -/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedGeometricPieceEquivalenceTheorem AssociatedGeometricPieceVanishingTheorem AssociatedJacquetFiltrationTheorem MinimalWeylTransportQuasicuspidalTheorem NonassociatedJacquetSubquotientsTheorem PadicAssociatedGeometricPiecesTheorem associatedGeometricPieceVanishing geometricPieceFunctor_subsingleton_of_proper_source nonassociatedJacquetSubquotients_rankZero normalizedRefinedInductionFunctor_subsingleton
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem geometricPieceFunctor jacquetInductionFunctor
open Langlands.AllField.Geometric
open scoped Pointwise

universe uF uV

/-- The published vanishing component, for every rank including zero. -/
theorem associatedGeometricPieceVanishing
    (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) :
    AssociatedGeometricPieceVanishingTheorem.{uF, uV} F T n := by
  let := T.topology
  intro B C ρ hρ hBC w S R hS hR hw
  exact geometricPieceFunctor_subsingleton_of_proper_source F T B C w.val S R
    hS.2.1 hR.2.1 ρ hρ
    (source_refinement_proper_of_associated_nonconjugating B C hBC w.val S hS hw)

end Langlands.AllField.CuspidalSupport
