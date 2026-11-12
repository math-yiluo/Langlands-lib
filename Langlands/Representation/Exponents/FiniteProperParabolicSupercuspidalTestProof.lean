import Langlands.Representation.Exponents.FiniteProperParabolicSupercuspidalTestReduction
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # A finite proper-parabolic supercuspidality test: proof

The published reduction `finiteProperParabolicSupercuspidalTest_of_structure` derives
`FiniteProperParabolicSupercuspidalTestStatement` from three structural statements. All three
are now proved in the Library, so the test holds unconditionally.
-/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

open Langlands.GroupScheme

/-- For every connected reductive group over a nonarchimedean local field, finitely many proper
actual rational parabolic data test supercuspidality (a finite form of Renard VI.2.1,
Remark 1). -/
theorem finiteProperParabolicSupercuspidalTest :
    FiniteProperParabolicSupercuspidalTestStatement.{u, v} :=
  finiteProperParabolicSupercuspidalTest_of_structure parabolicDynamic
    smoothMaximalSplitTorusConjugacy relativeRootSystem

end Langlands.Aubert.General.RepresentedParabolic
