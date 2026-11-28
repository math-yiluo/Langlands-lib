import Langlands.Representation.CuspidalSupport.RationalSummandSmallProgeneratorReduction
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionProof
import Langlands.Representation.CuspidalSupport.RationalNormKernelTwistEquivalenceProof
import Langlands.BruhatTits.SpecialCompact.JointBasisProof

/-! # Renard VI.4.1, Proposition, for one summand

The compact induction from the common norm kernel of an irreducible
subrepresentation of the restriction of an irreducible cuspidal representation
is a small progenerator of the actual inertia block. The published reduction
`rationalSummandSmallProgenerator_of_jointBasis` is applied to the published
proofs of its three structural inputs: the joint special-compact basis
(Renard V.5.1–V.5.2), VI.3.2(ii) and VI.3.2(iii). -/

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.4.1, Proposition: for an irreducible cuspidal `π` and an
irreducible smooth `ρ` of the common norm kernel with an injective equivariant
map into the restriction of `π`, the compact induction of `ρ` is a small
progenerator of the actual inertia block. -/
theorem rationalSummandSmallProgenerator :
    RationalSummandSmallProgeneratorStatement.{uF, uV} :=
  rationalSummandSmallProgenerator_of_jointBasis
    BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence.{uF}
    rationalNormKernelFiniteRestriction.{uF, uV}
    rationalNormKernelTwistEquivalence.{uF, max uF uV, max uF uV}

end Langlands.CuspidalSupport
