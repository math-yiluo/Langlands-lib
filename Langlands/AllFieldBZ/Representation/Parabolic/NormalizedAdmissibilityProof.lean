import Langlands.AllFieldBZ.Representation.Parabolic.LeviInflationAdmissibilityProof
import Langlands.AllFieldBZ.Representation.Parabolic.NormalizedInductionStatement
import Langlands.AllFieldBZ.Representation.Parabolic.QuotientCompactProof
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof

/-!
# All-field port of `Langlands.Representation.Parabolic.NormalizedAdmissibilityProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.NormalizedAdmissibilityProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic hiding LeviInflationAdmissibilityClause NormalizedInductionAdmissibilityClause ParabolicQuotientCompactClause UnipotentFiniteContainmentClause isCompact_integralRange leviInflationAdmissibility normalizedInductionAdmissibility parabolicQuotientCompact quotientMap_image_integralRange
universe uF uV

/-- Actual normalized block parabolic induction preserves admissibility. -/
theorem normalizedInductionAdmissibility
    (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    NormalizedInductionAdmissibilityClause F T B V := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro sigma hSigma
  have hInflated : IsAdmissible (sigma.comp (B.leviProjection F.Carrier)) :=
    (leviInflationAdmissibility F T B V sigma).mpr hSigma
  have hTwisted : IsAdmissible (twist (T.parabolicHalfModulus B)
      (sigma.comp (B.leviProjection F.Carrier))) :=
    (isAdmissible_twist_iff (T.parabolicHalfModulus B)
      (sigma.comp (B.leviProjection F.Carrier))
      (T.isOpen_ker_parabolicHalfModulus B)).mpr hInflated
  exact (Induction.compactQuotientClause_holds (V := V)
    (B.parabolic F.Carrier) _ (parabolicQuotientCompact F T B) hTwisted).2

end Langlands.AllFieldBZ.Parabolic
