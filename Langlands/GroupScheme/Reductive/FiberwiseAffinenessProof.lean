import Langlands.GroupScheme.Reductive.FiberwiseAffinenessStatement
import Langlands.GroupScheme.Reductive.ValuationTorusAffinenessReduction
import Langlands.GroupScheme.HomScheme.SmoothAffineFiberTorusSubgroupRepresentabilityProof
import Langlands.GroupScheme.Torus.SelfCentralizingWeylAffinenessProof

/-! # Proof of affineness from connected reductive residue fibres -/

universe u

namespace Langlands.GroupScheme

/-- **Affineness from connected reductive residue fibres** (the everywhere-reductive
consequence of SGA 3, Exposé XVI, Theorem 5.2(i)).

A smooth separated quasi-compact group scheme over an arbitrary base whose
residue-field fibres are all connected reductive is affine over the base. The
reduction `reductiveFiberAffineness_of_torusFamilies_of_weylCriterion` is applied
to the universal torus families of
`TorusSubgroupModuli.smoothAffineFiberTorusSubgroupRepresentability` and to the
Weyl-quotient affineness criterion `selfCentralizingTorusWeylAffineness`. -/
theorem reductiveFiberAffineness : ReductiveFiberAffinenessStatement.{u} :=
  reductiveFiberAffineness_of_torusFamilies_of_weylCriterion
    TorusSubgroupModuli.smoothAffineFiberTorusSubgroupRepresentability
    selfCentralizingTorusWeylAffineness

end Langlands.GroupScheme
