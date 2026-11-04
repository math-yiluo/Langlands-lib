import Langlands.Representation.Smooth.Admissibility.HoweStatement
import Langlands.GroupScheme.Rational.StandardCocharacterStatement
import Langlands.GroupScheme.Rational.StandardLeviIntersectionStatement
import Langlands.GroupScheme.Rational.Statement
import Langlands.BruhatTits.SpecialCompact.JointBasisStatement
import Langlands.Representation.Aubert.General.RationalCuspidalCompactRestrictionStatement
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionStatement

/-! # Rational Howe assembly using the joint basis's Levi representatives -/

noncomputable section

universe u uV

namespace Langlands.SmoothRep

/-- The joint basis already includes reductive representatives of the standard
Levis, so the assembly retains six explicit prerequisites. -/
def RationalHoweJointAssemblyStatement : Prop :=
  GroupScheme.StandardCocharacterStatement.{u} →
  GroupScheme.StandardLeviIntersectionStatement.{u} →
  GroupScheme.RelativeRootSystemStatement.{u} →
  BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u} →
  Aubert.General.RationalPointFamily.RationalCuspidalCompactRestrictionStatement.{u,
    max (u + 1) uV} →
  CuspidalSupport.RationalNormKernelFiniteRestrictionStatement.{u, max (u + 1) uV} →
  RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement.{u, uV}

end Langlands.SmoothRep
