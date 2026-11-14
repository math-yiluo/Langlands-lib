import Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof
import Langlands.AllField.Representation.CuspidalSupport.AssociatedGeometricPiecesStatement
import Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.AllField.Representation.Geometric.WeylStatementSupplement
/-! Quasicuspidality of whole-Levi transport along a minimal conjugating permutation. -/

namespace Langlands.AllField.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedGeometricPieceEquivalenceTheorem AssociatedGeometricPieceVanishingTheorem AssociatedJacquetFiltrationTheorem MinimalWeylTransportQuasicuspidalTheorem NonassociatedJacquetSubquotientsTheorem PadicAssociatedGeometricPiecesTheorem minimalWeylTransportQuasicuspidal
open Langlands.AllField.CuspidalSupport

open Langlands.GeneralLinear
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor
open Langlands.AllField.Geometric

universe uF uV

section Geometry


end Geometry

section Cast


end Cast

section Refinement


end Refinement

variable {F : Type uF} [Field F] {n : ℕ}

/-- The published transport-quasicuspidality component, for every rank
including zero. -/
theorem minimalWeylTransportQuasicuspidal 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) :
    MinimalWeylTransportQuasicuspidalTheorem.{uF, uV} F T n := by
  let := T.topology
  intro B C ρ hρ w hw
  exact isLeviQuasicuspidal_transport B C w.val w.property hw ρ.representation hρ

end Langlands.AllField.CuspidalSupport
