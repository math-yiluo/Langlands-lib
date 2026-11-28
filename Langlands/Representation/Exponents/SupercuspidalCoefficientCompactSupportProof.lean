import Langlands.Representation.Exponents.SupercuspidalCoefficientCompactSupportReduction
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.BruhatTits.SpecialCompact.JointBasisProof

/-! # Proof of supercuspidal coefficient compactness on the full central quotient

Renard VI.2.1, (a) implies (b), in the represented-parabolic interface: the
three structural premises of
`supercuspidalUnitaryCoefficientCompactSupportStructuralReduction` are proved
theorems, so the full-scope statement holds unconditionally.
-/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

/-- **Renard VI.2.1, (a) implies (b).** For every nonarchimedean local field, every
connected reductive group and every irreducible smooth complex representation of
its rational points whose normalized Jacquet modules vanish along every proper
actual rational parabolic, the norm of each smooth-dual matrix coefficient,
descended by a unitary central character, has compact support on the quotient by
the full center of the rational point group. -/
theorem supercuspidalUnitaryCoefficientCompactSupport :
    SupercuspidalUnitaryCoefficientCompactSupportStatement.{u, v} :=
  supercuspidalUnitaryCoefficientCompactSupportStructuralReduction
    GroupScheme.standardCocharacter GroupScheme.relativeRootSystem
    BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence

end Langlands.Aubert.General.RepresentedParabolic
