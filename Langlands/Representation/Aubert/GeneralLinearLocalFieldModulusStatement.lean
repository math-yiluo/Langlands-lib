import Langlands.Representation.Aubert.GeneralLinearSpecialization
import Langlands.AllField.Group.GL.CompactOpen
import Langlands.AllField.Group.GL.BlockModulus

/-! # Full upper-block modulus over a nonarchimedean local field -/

noncomputable section

universe u

namespace Langlands.Parabolic

/-- The Haar module of conjugation on the actual upper-block radical, on
every element of the parabolic, is the explicit block modulus inflated along
the block projection. The assertion includes every nonarchimedean local field
and rank zero. -/
def LocalFieldGeneralLinearModulusCompatibilityStatement : Prop :=
  ∀ (F : Type u) [Field F] (T : LocalFieldData F) (n : ℕ)
    (B : GeneralLinear.BlockShape n),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.generalLinearLocallyCompactSpace n
    B.GeneralModulusCompatibility (T.leviModulus B)

end Langlands.Parabolic
