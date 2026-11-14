import Langlands.AllFieldBZ.Group.GL.BlockModulus
import Langlands.Representation.Parabolic.NormalizedInductionStatement

/-!
# All-field port of `Langlands.Representation.Parabolic.NormalizedInductionStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.NormalizedInductionStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic hiding NormalizedInductionAdmissibilityClause
universe uF uU uV uW

variable (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (U : Type uU) (V : Type uV) (W : Type uW)
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]

/-- Admissibility for right-translation induction with the actual positive
block half-modulus. -/
def NormalizedInductionAdmissibilityClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ σ : Representation ℂ (B.Levi F.Carrier) V,
    IsAdmissible σ →
    IsAdmissible (Induction.smoothInduced (B.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus B)
        (σ.comp (B.leviProjection F.Carrier))))

end Langlands.AllFieldBZ.Parabolic
