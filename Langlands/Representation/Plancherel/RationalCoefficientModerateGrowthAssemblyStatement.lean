import Langlands.Representation.Plancherel.RationalModerateGrowthStatement
import Langlands.GroupScheme.Rational.StandardCocharacterStatement
import Langlands.BruhatTits.SpecialCompact.JointBasisStatement

/-! # Coefficientwise moderate growth from the joint structural existence target -/

noncomputable section

universe u uV

namespace Langlands.Plancherel

/-- The standard-cocharacter and joint special-compact/basis existence targets
suffice for the whole coefficientwise moderate-growth proposition. -/
def RationalCoefficientModerateGrowthAssemblyStatement : Prop :=
  GroupScheme.StandardCocharacterStatement.{u} →
    BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u} →
      RationalCoefficientModerateGrowthStatement.{u, uV}

end Langlands.Plancherel
