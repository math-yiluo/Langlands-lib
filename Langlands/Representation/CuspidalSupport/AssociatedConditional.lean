import Langlands.Representation.CuspidalSupport.AssociatedAssembly
import Langlands.Representation.CuspidalSupport.AssociatedRankZero
import Langlands.Representation.CuspidalSupport.FiltrationQuasicuspidality

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData) (n : ℕ)

/-- Assemble the actual associated Jacquet filtration and its quasicuspidality
from the individual geometric inputs and zero-factor deletion. -/
theorem associatedJacquetFiltration_of_geometricPieces
    (hgeo : ∀ B C : BlockShape n, GeometricLemmaTheorem.{uF, uV} T B C)
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
    (hgeo : PadicGeometricLemmaTheorem.{uF, uV})
    (hpieces : PadicAssociatedGeometricPiecesTheorem.{uF, uV})
    (hdelete : ObjectRepFiltration.ZeroFactorDeletionTheorem.{0, uF, max uF uV}) :
    AssociatedJacquetFiltrationTheorem.{uF, uV} F T n := by
  by_cases hn : n = 0
  · subst n
    exact associatedJacquetFiltration_rankZero F T
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨hvan, hequiv, htransport⟩ := hpieces p F T n hpos
    exact associatedJacquetFiltration_of_geometricPieces F T n
      (hgeo p F T n hpos) hvan hequiv htransport hdelete

end Langlands.CuspidalSupport
