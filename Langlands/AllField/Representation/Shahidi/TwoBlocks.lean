import Langlands.Representation.Shahidi.TwoBlocks
import Langlands.AllField.Group.GL.BlockModulusSupplement
/-! # Ordered two-block shapes for Shahidi induction -/

namespace Langlands.AllField.Shahidi
open Langlands.Shahidi
open Langlands.AllField.Shahidi

open Langlands.GeneralLinear

universe u



end Langlands.AllField.Shahidi

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open Langlands.Shahidi
open Langlands.AllField.Shahidi

universe u

variable {F : Type u} [Field F]
variable (T : LocalFieldData F) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)

/-- The full block modulus has precisely the standard two determinant exponents. -/
theorem leviModulus_twoBlocks (g : (twoBlocks m n hm hn).Levi F) :
    T.leviModulus (twoBlocks m n hm hn) g =
      T.determinantNorm m (g 0) ^ n / T.determinantNorm n (g 1) ^ m := by
  rw [T.leviModulus_apply]
  simp only [Fin.prod_univ_two, Finset.prod_filter]
  norm_num [twoBlocks]
  rfl

end Langlands.LocalFieldData
