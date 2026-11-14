import Langlands.AllFieldBZ.Representation.Geometric.WeylStatement
import Langlands.AllFieldBZ.Representation.Geometric.WeylUniquenessProof
import Langlands.AllFieldBZ.Representation.Parabolic.RefinementComposition
import Langlands.Group.GL.HeadTailBlocks

/-!
# All-field port of `Langlands.Group.GL.HeadTailBlocks`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.HeadTailBlocks` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
open Langlands.Geometric hiding PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem
open Langlands.AllFieldBZ.Geometric
universe u
variable {n k : ℕ} (B : Langlands.GeneralLinear.BlockShape n) (h : B.length = k + 2)

private theorem _root_.Langlands.GeneralLinear.BlockShape.index_val_congr {i j : Fin B.length} (hij : i = j)
    (x : Fin (B.size i)) (y : Fin (B.size j)) (hxy : x.val = y.val) :
    (B.index i x).val = (B.index j y).val := by
  subst j
  have he : x = y := Fin.ext hxy
  subst y
  rfl

variable (R : Type u) [CommRing R]

section Topology
variable [TopologicalSpace R] [IsTopologicalRing R]

end Topology
end Langlands.AllFieldBZ.GeneralLinear.BlockShape
