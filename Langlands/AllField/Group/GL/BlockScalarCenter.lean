import Langlands.Group.GL.BlockScalarCenter
import Langlands.AllField.Group.GL.BlockIwahoriDefinitions
/-!
# Block scalars in the center of the product Levi

The existing `Langlands.AllField.Parabolic.blockScalarCenter` is kept in a group-level
module so that its consumers do not need Jacquet representation theory.
-/

noncomputable section

namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding blockScalarCenter
open Langlands.AllField.Parabolic

universe uF

variable {F : Type uF} [Field F]
variable {m : ℕ} (B : GeneralLinear.BlockShape m)

/-- The block-scalar tuples, as a homomorphism into the center of the actual
product Levi. -/
def blockScalarCenter :
    (Fin B.length → Fˣ) →* Subgroup.center (B.Levi F) :=
  (B.blockScalarLevi F).codRestrict (Subgroup.center (B.Levi F))
    fun a => Subgroup.mem_center_iff.mpr fun l =>
      (B.blockScalarLevi_commute F a l).symm

end Langlands.AllField.Parabolic
