import Langlands.GroupScheme.SimplyConnected.DerivedCoverSplitTorusAssembly
import Langlands.GroupScheme.Derived.MaximalSplitTorusConjugacyReduction
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.SimplyConnected.SplitTorusProof
import Langlands.GroupScheme.Rational.SplitTorusIsogenyCocharacterProof

/-! # Maximal split tori through the simply connected cover of a derived subgroup -/

universe u

namespace Langlands.GroupScheme

/-- Over every field, a maximal split torus of a connected reductive group contains a maximal
split torus of the derived subgroup, which is covered by a maximal split torus of the simply
connected cover through a central isogeny; the composite to the ambient torus is injective on
rational and real cocharacters with the range of the derived torus. -/
theorem simplyConnectedDerivedCoverSplitTorus :
    SimplyConnectedDerivedCoverSplitTorusStatement.{u} :=
  simplyConnectedDerivedCoverSplitTorusStatement_of_inputs
    (derivedMaximalSplitTorus_of_smoothMaximalSplitTorusConjugacy
      smoothMaximalSplitTorusConjugacy)
    simplyConnectedCoverSplitTorus splitTorusIsogenyCocharacter

end Langlands.GroupScheme
