import Langlands.Representation.Smooth.Admissibility.HoweStatement
import Langlands.GroupScheme.Rational.StandardLeviSplitComponentStatement
import Langlands.GroupScheme.Rational.StandardLeviIntersectionStatement
import Langlands.BruhatTits.SpecialCompact.JointBasisStatement
import Langlands.Representation.Aubert.General.RationalCuspidalCompactRestrictionStatement
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionStatement

/-! # Explicit structural inputs for the rational Howe implication -/

noncomputable section

universe u uV

namespace Langlands.SmoothRep

/-- The actual structural and cuspidal inputs imply the exact unrestricted
rational-point finite-length statement, with independent carrier universe. -/
def RationalHoweAssemblyStatement : Prop :=
  GroupScheme.StandardCocharacterStatement.{u} →
  GroupScheme.StandardLeviIntersectionStatement.{u} →
  GroupScheme.RelativeRootSystemStatement.{u} →
  GroupScheme.StandardLeviSplitComponentStatement.{u} →
  BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u} →
  Aubert.General.RationalPointFamily.RationalCuspidalCompactRestrictionStatement.{u,
    max (u + 1) uV} →
  CuspidalSupport.RationalNormKernelFiniteRestrictionStatement.{u, max (u + 1) uV} →
  RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement.{u, uV}

end Langlands.SmoothRep
