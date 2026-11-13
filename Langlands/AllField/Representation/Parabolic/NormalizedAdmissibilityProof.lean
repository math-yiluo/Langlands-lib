import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.AllField.Representation.Parabolic.LeviInflationAdmissibilityProof
import Langlands.AllField.Representation.Parabolic.NormalizedInductionStatement
import Langlands.AllField.Representation.Parabolic.QuotientCompactProof
namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding LeviInflationAdmissibilityClause NormalizedInductionAdmissibilityClause ParabolicQuotientCompactClause UnipotentFiniteContainmentClause isCompact_integralRange leviInflationAdmissibility normalizedInductionAdmissibility parabolicQuotientCompact quotientMap_image_integralRange
open Langlands.AllField.Parabolic

universe uF uV

/-- Actual normalized block parabolic induction preserves admissibility. -/
theorem normalizedInductionAdmissibility
    (F : Type uF) [Field F]
    (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    NormalizedInductionAdmissibilityClause F T B V := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro sigma hSigma
  have hInflated : IsAdmissible (sigma.comp (B.leviProjection F)) :=
    (leviInflationAdmissibility F T B V sigma).mpr hSigma
  have hTwisted : IsAdmissible (twist (T.parabolicHalfModulus B)
      (sigma.comp (B.leviProjection F))) :=
    (isAdmissible_twist_iff (T.parabolicHalfModulus B)
      (sigma.comp (B.leviProjection F))
      (T.isOpen_ker_parabolicHalfModulus B)).mpr hInflated
  exact (Induction.compactQuotientClause_holds (V := V)
    (B.parabolic F) _ (parabolicQuotientCompact F T B) hTwisted).2

end Langlands.AllField.Parabolic
