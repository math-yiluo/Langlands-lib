import Langlands.Representation.Exponents.NormalizedTemperedStandardReductionFromDynamics
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # Reduction of normalized-exponent temperedness to standard parabolics

The published dynamic-structure reduction is applied to the published proofs of
its four structural statements.
-/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Normalized-exponent temperedness is equivalent to admissibility together
with the exponent cone condition on every actual standard parabolic, Levi and
split-component triple of one fixed standard family. -/
theorem normalizedTemperedStandardReduction :
    NormalizedTemperedStandardReductionStatement.{u, v} :=
  normalizedTemperedStandardReduction_of_dynamic_structural_statements
    parabolicDynamic dynamicGeometricUnipotentRadical
    smoothMaximalSplitTorusConjugacy relativeRootSystem

end Langlands.Aubert.General.RepresentedParabolic
