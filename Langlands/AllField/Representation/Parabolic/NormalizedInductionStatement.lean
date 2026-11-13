import Langlands.Representation.Parabolic.NormalizedInductionStatement
import Langlands.AllField.Group.GL.BlockModulus
namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding NormalizedInductionAdmissibilityClause
open Langlands.AllField.Parabolic

universe uF uU uV uW

variable (F : Type uF) [Field F]
    (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (U : Type uU) (V : Type uV) (W : Type uW)
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]

/-- Admissibility for right-translation induction with the actual positive
block half-modulus. -/
def NormalizedInductionAdmissibilityClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ σ : Representation ℂ (B.Levi F) V,
    IsAdmissible σ →
    IsAdmissible (Induction.smoothInduced (B.parabolic F)
      (twist (T.parabolicHalfModulus B)
        (σ.comp (B.leviProjection F))))

end Langlands.AllField.Parabolic
