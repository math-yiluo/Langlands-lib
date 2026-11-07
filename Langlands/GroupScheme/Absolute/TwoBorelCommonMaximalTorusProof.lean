import Langlands.GroupScheme.Absolute.TwoBorelCommonMaximalTorusReduction
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Absolute.BruhatCoveringProof

/-! # A common ambient maximal torus of two Borel subgroups -/

universe u

namespace Langlands.GroupScheme

/-- Two Borel subgroups of a connected reductive group over an algebraically closed
field contain a common maximal torus of the ambient group. -/
theorem twoBorelCommonMaximalTorus : TwoBorelCommonMaximalTorusStatement.{u} :=
  twoBorelCommonMaximalTorusStatement_of_borel_bruhat_inputs
    borelConjugacy absoluteBruhatCovering

end Langlands.GroupScheme
