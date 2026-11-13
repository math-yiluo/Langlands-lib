import Langlands.Representation.Parabolic.AdmissibilityStatement
import Langlands.AllField.Group.GL.Padic
namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding LeviInflationAdmissibilityClause
open Langlands.AllField.Parabolic

universe uF uV

variable (F : Type uF) [Field F]
    (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- Inflation along the actual diagonal-block projection preserves and
reflects admissibility. -/
def LeviInflationAdmissibilityClause : Prop :=
  letI := T.topology
  ∀ σ : Representation ℂ (B.Levi F) V,
    IsAdmissible (σ.comp (B.leviProjection F)) ↔ IsAdmissible σ

end Langlands.AllField.Parabolic
