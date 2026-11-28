import Langlands.Representation.CuspidalSupport.RationalSummandSmallProgeneratorReduction
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionProof
import Langlands.Representation.CuspidalSupport.RationalNormKernelTwistEquivalenceProof
import Langlands.BruhatTits.SpecialCompact.JointBasisProof

/-! # Renard VI.4.1, Theorem, for one summand

The compact induction `Π` from the common norm kernel of an irreducible
subrepresentation of the restriction of an irreducible cuspidal representation
lies in the actual inertia block, and `Hom(Π, •)` is an equivalence from the
block to right modules over `End Π`. The published reduction
`rationalSummandHomEquivalence_of_jointBasis` (the Proposition followed by
Renard A.VIII.2 on the inherited abelian structure of the block) is applied to
the published proofs of its three structural inputs: the joint special-compact
basis (Renard V.5.1–V.5.2), VI.3.2(ii) and VI.3.2(iii). -/

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.4.1, Theorem: for an irreducible cuspidal `π` and an irreducible
smooth `ρ` of the common norm kernel with an injective equivariant map into the
restriction of `π`, the compact induction `Π` of `ρ` lies in the actual inertia
block and `preadditiveCoyonedaObj Π` is an equivalence from the block to
`ModuleCat (End Π)ᵐᵒᵖ`. -/
theorem rationalSummandHomEquivalence :
    RationalSummandHomEquivalenceStatement.{uF, uV} :=
  rationalSummandHomEquivalence_of_jointBasis
    BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence.{uF}
    rationalNormKernelFiniteRestriction.{uF, uV}
    rationalNormKernelTwistEquivalence.{uF, max uF uV, max uF uV}

end Langlands.CuspidalSupport
