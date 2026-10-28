import Langlands.Group.GL.BlockIwahoriDefinitions

/-!
# Block scalars in the center of the product Levi

The existing `Langlands.Parabolic.blockScalarCenter` is kept in a group-level
module so that its consumers do not need Jacquet representation theory.
-/

noncomputable section

namespace Langlands.Parabolic

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {m : ℕ} (B : GeneralLinear.BlockShape m)

/-- The block-scalar tuples, as a homomorphism into the center of the actual
product Levi. -/
def blockScalarCenter :
    (Fin B.length → F.Carrierˣ) →* Subgroup.center (B.Levi F.Carrier) :=
  (B.blockScalarLevi F.Carrier).codRestrict (Subgroup.center (B.Levi F.Carrier))
    fun a => Subgroup.mem_center_iff.mpr fun l =>
      (B.blockScalarLevi_commute F.Carrier a l).symm

end Langlands.Parabolic
