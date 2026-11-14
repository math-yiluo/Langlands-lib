import Langlands.AllFieldBZ.Representation.CuspidalSupport.AssociatedGeometricPiecesStatement
import Langlands.AllFieldBZ.Representation.CuspidalSupport.MinimalConjugatingCosetsProof
import Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedGeometricPieceEquivalenceTheorem AssociatedGeometricPieceVanishingTheorem AssociatedJacquetFiltrationTheorem MinimalWeylTransportQuasicuspidalTheorem NonassociatedJacquetSubquotientsTheorem PadicAssociatedGeometricPiecesTheorem minimalWeylTransportQuasicuspidal
open Langlands.GeneralLinear
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor
open Langlands.AllFieldBZ.Geometric
universe uF uV

section Geometry
variable {F : Type uF} [Field F] {n : ℕ} {B C : BlockShape n}
  {w : Equiv.Perm (Fin n)}

end Geometry
section Cast
variable {F : Type uF} [Field F]

end Cast
section Refinement
variable {F : Type uF} [Field F] {n : ℕ} {B C : BlockShape n}
  {w : Equiv.Perm (Fin n)}

end Refinement
variable {F : Type uF} [Field F] {n : ℕ}

/-- The published transport-quasicuspidality component, for every rank
including zero. -/
theorem minimalWeylTransportQuasicuspidal (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) (n : ℕ) :
    MinimalWeylTransportQuasicuspidalTheorem.{uF, uV} F T n := by
  let := T.topology
  intro B C ρ hρ w hw
  exact isLeviQuasicuspidal_transport B C w.val w.property hw ρ.representation hρ

end Langlands.AllFieldBZ.CuspidalSupport
