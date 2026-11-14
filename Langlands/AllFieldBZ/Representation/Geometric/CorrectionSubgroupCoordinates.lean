import Langlands.AllFieldBZ.Group.GL.BlockUnipotentCoordinates
import Langlands.AllFieldBZ.Representation.Geometric.StandardIntersectionsProof
import Langlands.Representation.Geometric.CorrectionSubgroupCoordinates

/-!
# All-field port of `Langlands.Representation.Geometric.CorrectionSubgroupCoordinates`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.CorrectionSubgroupCoordinates` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
open scoped BigOperators
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem padicStandardIntersectionsTheorem
open Langlands.GeneralLinear
universe u
variable {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))

variable (R : Type u) [CommRing R]

private theorem _root_.Langlands.Geometric.conjugate_entry (g : GeneralLinear n R) (a b : Fin n) :
    (MulAut.conj (permutation n R w) g) (w a) (w b) = g a b := by
  change (permutation n R w * g * (permutation n R w)⁻¹) (w a) (w b) = _
  rw [permutation_conjugate_entry]
  change g (w.symm (w a)) (w.symm (w b)) = _
  simp only [Equiv.symm_apply_apply]

section Topology
variable [TopologicalSpace R]

variable [IsTopologicalRing R]

end Topology
end Langlands.AllFieldBZ.Geometric
