import Langlands.Group.GL.BlockModulus
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
import Langlands.AllField.Group.GL.PadicBlocksSupplement
/-!
# Explicit positive block modulus characters

For the standard upper block parabolic the factor contributed by blocks `i < j`
is `|det m_i| ^ n_j / |det m_j| ^ n_i`. The character is built from these actual
determinants. Its interpretation as Haar scaling is a separate theorem.
-/

noncomputable section

open scoped BigOperators NNReal

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe u

variable {F : Type u} [Field F]
variable (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- Continuity for the product of the actual block determinant norms. -/
theorem continuous_leviModulus :
    letI := T.topology
    Continuous (T.leviModulus B) := by
  let := T.topology
  change Continuous (fun m : B.Levi F => T.leviModulus B m)
  simp_rw [T.leviModulus_apply B]
  simp only [div_eq_mul_inv]
  exact continuous_finsetProd _ fun i _ =>
    continuous_finsetProd _ fun j _ =>
      (((T.determinantNormContinuous (B.size i)).continuous.comp
        (continuous_apply i)).pow _).mul
      (((T.determinantNormContinuous (B.size j)).continuous.comp
        (continuous_apply j)).pow _).inv

/-- Every pair of block contributions cancels on an ambient scalar matrix. -/
@[simp]
theorem leviModulus_scalar (a : Fˣ) :
    T.leviModulus B (fun i => GeneralLinear.scalar (n := B.size i) a) = 1 := by
  rw [T.leviModulus_apply]
  simp only [T.determinantNorm_scalar]
  apply Finset.prod_eq_one
  intro i _
  apply Finset.prod_eq_one
  intro j _
  rw [← pow_mul, ← pow_mul, Nat.mul_comm (B.size i) (B.size j)]
  exact div_self' _

theorem leviHalfModulus_sq (m : B.Levi F) :
    T.leviHalfModulus B m ^ 2 = Jacquet.complexCharacter (T.leviModulus B) m := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, leviHalfModulus_apply, Jacquet.complexCharacter_apply]
  norm_cast
  exact NNReal.sq_sqrt _

end Langlands.LocalFieldData

namespace Langlands

universe u


end Langlands
