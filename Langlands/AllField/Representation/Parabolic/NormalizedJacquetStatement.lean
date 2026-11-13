import Langlands.Representation.Parabolic.NormalizedJacquetStatement
import Langlands.AllField.Group.GL.BlockModulus
namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding NormalizedJacquetAdmissibilityClause
open Langlands.AllField.Parabolic

universe uF uU uV uW

variable (F : Type uF) [Field F]
    (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (U : Type uU) (V : Type uV) (W : Type uW)
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]

/-- Admissibility for the actual radical quotient with inverse block half-modulus. -/
def NormalizedJacquetAdmissibilityClause : Prop :=
  letI := T.topology
  ∀ ρ : Representation ℂ (GeneralLinear n F) V,
    IsAdmissible ρ →
    IsAdmissible (twist (Jacquet.inverseHalfCharacter (T.leviModulus B))
      (leviCoinvariants B (ρ.comp (B.parabolic F).subtype)))

end Langlands.AllField.Parabolic
