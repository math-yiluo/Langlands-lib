import Langlands.Representation.Parabolic.NormalizedInductionStatement
import Langlands.Representation.Parabolic.LeviInflationAdmissibilityProof
import Langlands.Representation.Parabolic.QuotientCompactProof
import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Representation.Twist.AdmissibilityProof

namespace Langlands.Parabolic

universe uF uV

/-- Actual normalized block parabolic induction preserves admissibility. -/
theorem normalizedInductionAdmissibility
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
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

end Langlands.Parabolic
