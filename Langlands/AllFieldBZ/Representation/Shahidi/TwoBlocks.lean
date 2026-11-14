import Langlands.AllFieldBZ.Group.GL.BlockModulus
import Langlands.AllFieldBZ.Group.GL.RankMaps
import Langlands.Representation.Shahidi.TwoBlocks

/-!
# All-field port of `Langlands.Representation.Shahidi.TwoBlocks`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Shahidi.TwoBlocks` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Shahidi
open Langlands.Shahidi
open Langlands.GeneralLinear
universe u

variable {m n : ℕ} (hm : 0 < m) (hn : 0 < n)

variable (R : Type u) [CommRing R]

end Langlands.AllFieldBZ.Shahidi
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open Langlands.Shahidi
universe u

variable {F : LocalFieldPackage.{u}}
variable (T : F.TopologicalData) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)

/-- The full block modulus has precisely the standard two determinant exponents. -/
theorem leviModulus_twoBlocks (g : (twoBlocks m n hm hn).Levi F.Carrier) :
    T.leviModulus (twoBlocks m n hm hn) g =
      T.determinantNorm m (g 0) ^ n / T.determinantNorm n (g 1) ^ m := by
  rw [T.leviModulus_apply]
  simp only [Fin.prod_univ_two, Finset.prod_filter]
  norm_num [twoBlocks]
  rfl

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
