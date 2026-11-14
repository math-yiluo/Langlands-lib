import Langlands.AllFieldBZ.Representation.CuspidalSupport.AssociatedAssembly
import Langlands.AllFieldBZ.Representation.CuspidalSupport.AssociatedRankZero
import Langlands.Representation.CuspidalSupport.AssociatedConditional

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.AssociatedConditional`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.AssociatedConditional` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedGeometricPieceEquivalenceTheorem AssociatedGeometricPieceVanishingTheorem AssociatedJacquetFiltrationTheorem MinimalWeylTransportQuasicuspidalTheorem NonassociatedJacquetSubquotientsTheorem PadicAssociatedGeometricPiecesTheorem associatedFiltration_of_geometricPieces associatedJacquetFiltration_of_geometricPieces associatedJacquetFiltration_of_prerequisites associatedJacquetFiltration_rankZero rankZero_jacquetInductionEquiv
open Langlands.GeneralLinear
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem geometricPieceFunctor jacquetInductionFunctor
open Langlands.AllFieldBZ.Geometric
universe uF uV

variable (F : LocalFieldPackage.{uF})
  (T : F.TopologicalData) (n : ℕ)

/-- Assemble the actual associated Jacquet filtration and its quasicuspidality
from the individual geometric inputs and zero-factor deletion. -/
theorem associatedJacquetFiltration_of_geometricPieces
    (hgeo : ∀ B C : BlockShape n, Langlands.AllFieldBZ.Geometric.GeometricLemmaTheorem.{uF, uV} T B C)
    (hvan : AssociatedGeometricPieceVanishingTheorem.{uF, uV} F T n)
    (hequiv : AssociatedGeometricPieceEquivalenceTheorem.{uF, uV} F T n)
    (htransport : MinimalWeylTransportQuasicuspidalTheorem.{uF, uV} F T n)
    (hdelete : ObjectRepFiltration.ZeroFactorDeletionTheorem.{0, uF, max uF uV}) :
    AssociatedJacquetFiltrationTheorem.{uF, uV} F T n := by
  let := T.topology
  intro B C ρ hρ hBC
  obtain ⟨r, e, s, hs, hq⟩ :=
    associatedFiltration_of_geometricPieces F T n hgeo hvan hequiv htransport hdelete
      B C ρ hρ hBC
  exact ⟨isLeviQuasicuspidal_of_filtration C s hq, r, e, s, hs⟩

/-- The full rank split, with the remaining geometric and deletion proof
obligations explicit. This helper is not the unconditional theorem. -/
theorem associatedJacquetFiltration_of_prerequisites
    (hgeo : Langlands.AllFieldBZ.Geometric.PadicGeometricLemmaTheorem.{uF, uV})
    (hpieces : PadicAssociatedGeometricPiecesTheorem.{uF, uV})
    (hdelete : ObjectRepFiltration.ZeroFactorDeletionTheorem.{0, uF, max uF uV}) :
    AssociatedJacquetFiltrationTheorem.{uF, uV} F T n := by
  by_cases hn : n = 0
  · subst n
    exact associatedJacquetFiltration_rankZero F T
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨hvan, hequiv, htransport⟩ := hpieces F T n hpos
    exact associatedJacquetFiltration_of_geometricPieces F T n
      (hgeo F T n hpos) hvan hequiv htransport hdelete

end Langlands.AllFieldBZ.CuspidalSupport
