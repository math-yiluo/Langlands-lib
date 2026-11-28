import Langlands.Representation.Smooth.Admissibility.HoweStatement
import Langlands.Representation.Smooth.Admissibility.RationalHoweJointAssemblyProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardLeviIntersectionProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.BruhatTits.SpecialCompact.JointBasisProof
import Langlands.Representation.Aubert.General.RationalCuspidalCompactRestrictionProof
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionProof

/-!
# Howe's finite-length implication on actual reductive rational points: proof

Renard VI.6.3, finite type and admissible implies finite length, for the
canonical rational-point topology. The proof applies the rational Howe assembly
`rationalHoweJointAssembly` to the six proved results it takes as premises.
-/

set_option autoImplicit false

universe u uV

namespace Langlands.SmoothRep

/-- **Renard VI.6.3** (finite type and admissible implies finite length). For a
connected reductive group over a nonarchimedean local field of any characteristic,
every smooth complex representation of its rational points, with the canonical
rational-point topology, whose group-algebra module is finitely generated and which
is admissible has finite length. The field and the representation carrier have
independent universes. -/
theorem rationalPointsFinitelyGeneratedAdmissibleFiniteLength :
    RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement.{u, uV} :=
  rationalHoweJointAssembly.{u, uV}
    GroupScheme.standardCocharacter
    GroupScheme.standardLeviIntersection
    GroupScheme.relativeRootSystem
    BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence
    Aubert.General.rationalCuspidalCompactRestriction
    CuspidalSupport.rationalNormKernelFiniteRestriction

end Langlands.SmoothRep
