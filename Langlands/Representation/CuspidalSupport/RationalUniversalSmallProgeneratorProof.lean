import Langlands.Representation.CuspidalSupport.RationalUniversalSmallProgeneratorSpecialVertexReduction
import Langlands.BruhatTits.SpecialCompact.JointBasisProof

/-! # Renard VI.4.1 for the full-restriction Π₁

The actual compact induction of the full restriction of an irreducible cuspidal
smooth complex representation to the common rational-character norm kernel is a
small projective generator of its actual inertia block. -/

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.4.1 Proposition with the alternative-progenerator Remark, for the
full-restriction Π₁: for every irreducible π, cuspidal along every proper actual
standard parabolic, `rationalNormKernelCompactInduction G π` lies in the block
`RationalInertiaBlock G (rationalInertiaBaseLift G π)` and satisfies there the
projective lifting, faithful integer Hom functor, coproduct existence and
coproduct preservation conditions, at independent universes `uF` and `uV`. -/
theorem rationalUniversalSmallProgenerator :
    RationalUniversalSmallProgeneratorStatement.{uF, uV} :=
  rationalUniversalSmallProgenerator_of_jointBasis
    Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence

end Langlands.CuspidalSupport
