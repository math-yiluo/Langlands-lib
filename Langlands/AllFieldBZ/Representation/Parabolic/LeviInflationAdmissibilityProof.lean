import Langlands.AllFieldBZ.Representation.Parabolic.AdmissibilityStatement
import Langlands.Representation.Parabolic.LeviInflationAdmissibilityProof

/-!
# All-field port of `Langlands.Representation.Parabolic.LeviInflationAdmissibilityProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.LeviInflationAdmissibilityProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ
universe uR uG uH uF uV

section Transport
variable {R : Type uR} {G : Type uG} {H : Type uH} {V : Type uV}
    [CommRing R] [Group G] [Group H] [AddCommGroup V] [Module R V]

end Transport
namespace Parabolic
open Langlands.Parabolic hiding LeviInflationAdmissibilityClause leviInflationAdmissibility
/-- Admissibility is preserved and reflected by actual Levi inflation. -/
theorem leviInflationAdmissibility
    (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    LeviInflationAdmissibilityClause F T B V := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro σ
  apply isAdmissible_comp_iff_of_open_surjective σ (B.leviProjection F.Carrier)
  · exact (B.leviProjectionContinuous F.Carrier).continuous
  · exact isOpenMap_snd.comp (B.decompositionHomeomorph F.Carrier).isOpenMap
  · intro m
    exact ⟨B.leviInParabolic F.Carrier m, B.leviProjection_section F.Carrier m⟩

end Parabolic
end Langlands.AllFieldBZ
