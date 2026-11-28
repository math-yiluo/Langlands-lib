import Langlands.Representation.CuspidalSupport.RationalCuspidalInertiaDecompositionReduction
import Langlands.Representation.CuspidalSupport.RationalCompactRestrictionInertiaDecompositionProof
import Langlands.Representation.Aubert.General.RationalCuspidalCompactRestrictionProof
import Langlands.BruhatTits.SpecialCompact.JointBasisProof

/-!
# Renard VI.3.3.1 for proper-standard cuspidal representations

An irreducible smooth representation of the actual rational-point group of a
connected reductive group over a nonarchimedean local field, all of whose
normalized Jacquet modules along proper actual standard parabolics vanish,
splits the whole smooth category into its inertia block and the complement.
The proof composes the published compact-restriction decomposition, the
published VI.2.1 implication (a) ⇒ (c) and the published joint special-compact
basis existence theorem through the published reduction.
-/

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.3.3.1: an irreducible smooth representation with vanishing
normalized Jacquet modules along every proper actual standard parabolic gives
the two-factor inertia decomposition of the whole smooth category. -/
theorem rationalCuspidalInertiaDecomposition :
    RationalCuspidalInertiaDecompositionStatement.{uF, uV} :=
  rationalCuspidalInertiaDecomposition_of_jointBasis
    rationalCompactRestrictionInertiaDecomposition.{uF, uV}
    Aubert.General.rationalCuspidalCompactRestriction.{uF, uV}
    BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence.{uF}

end Langlands.CuspidalSupport
