import Langlands.GroupScheme.Rational.RenardIndivisibleRootComparison
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # Proof of Renard's radical weights and simple indivisible roots -/

universe u

namespace Langlands.GroupScheme

/-- **Renard's root conventions** (V.3.4 and V.3.12, generalized to arbitrary fields).
For a maximal split torus of a connected reductive group over any field and a generic
cocharacter, the nonzero Lie weights of the actual dynamic radical are the positive
relative roots, their indivisible part agrees with both published reduced-positive-root
conventions, and its indecomposables are the published simple relative roots. -/
theorem renardRootConvention : RenardRootConventionStatement.{u} :=
  renardRootConventionStatement_of_relativeRootSystem relativeRootSystem

end Langlands.GroupScheme
