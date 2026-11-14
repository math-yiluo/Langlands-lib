import Langlands.AllFieldBZ.Group.GL.Padic
import Langlands.Representation.Parabolic.AdmissibilityStatement

/-!
# All-field port of `Langlands.Representation.Parabolic.AdmissibilityStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.AdmissibilityStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic hiding LeviInflationAdmissibilityClause
universe uF uV

variable (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- Inflation along the actual diagonal-block projection preserves and
reflects admissibility. -/
def LeviInflationAdmissibilityClause : Prop :=
  letI := T.topology
  ∀ σ : Representation ℂ (B.Levi F.Carrier) V,
    IsAdmissible (σ.comp (B.leviProjection F.Carrier)) ↔ IsAdmissible σ

end Langlands.AllFieldBZ.Parabolic
