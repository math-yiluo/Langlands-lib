import Langlands.Representation.Parabolic.LeviInflationAdmissibilityProof
import Langlands.AllField.Representation.Parabolic.AdmissibilityStatement
namespace Langlands.AllField

universe uR uG uH uF uV

section Transport

variable {R : Type uR} {G : Type uG} {H : Type uH} {V : Type uV}
    [CommRing R] [Group G] [Group H] [AddCommGroup V] [Module R V]

end Transport

namespace Parabolic
open Langlands.Parabolic hiding LeviInflationAdmissibilityClause leviInflationAdmissibility
open Langlands.AllField.Parabolic

/-- Admissibility is preserved and reflected by actual Levi inflation. -/
theorem leviInflationAdmissibility
    (F : Type uF) [Field F]
    (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    LeviInflationAdmissibilityClause F T B V := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro σ
  apply isAdmissible_comp_iff_of_open_surjective σ (B.leviProjection F)
  · exact (B.leviProjectionContinuous F).continuous
  · exact isOpenMap_snd.comp (B.decompositionHomeomorph F).isOpenMap
  · intro m
    exact ⟨B.leviInParabolic F m, B.leviProjection_section F m⟩

end Parabolic

end Langlands.AllField
