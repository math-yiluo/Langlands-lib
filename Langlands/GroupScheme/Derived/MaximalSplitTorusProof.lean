import Langlands.GroupScheme.Derived.MaximalSplitTorusConjugacyReduction
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof

/-! # Maximal split tori of a derived subgroup inside an ambient maximal split torus -/

universe u

namespace Langlands.GroupScheme

/-- Over every field, every maximal split torus of a connected reductive group contains,
through a closed homomorphism of commutative group schemes, a maximal split torus of any
exhibited derived subgroup, compatibly with the inclusions into the group. -/
theorem derivedMaximalSplitTorus : DerivedMaximalSplitTorusStatement.{u} :=
  derivedMaximalSplitTorus_of_smoothMaximalSplitTorusConjugacy smoothMaximalSplitTorusConjugacy

end Langlands.GroupScheme
