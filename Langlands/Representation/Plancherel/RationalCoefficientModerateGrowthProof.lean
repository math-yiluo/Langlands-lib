import Langlands.Representation.Plancherel.RationalCoefficientModerateGrowthAssemblyProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.BruhatTits.SpecialCompact.JointBasisProof

/-! # Coefficientwise moderate growth on actual reductive rational points -/

universe u uV

namespace Langlands.Plancherel

/-- Waldspurger, Corollary I.4.4, first assertion: for every nonarchimedean
local field, connected reductive group, closed algebraic matrix embedding and
admissible smooth complex representation, each matrix coefficient is bounded by
a positive constant times a natural power of the residue-normalized matrix
norm of the embedding, uniformly in the rational point. -/
theorem rationalCoefficientModerateGrowth :
    RationalCoefficientModerateGrowthStatement.{u, uV} :=
  rationalCoefficientModerateGrowthAssembly
    GroupScheme.standardCocharacter
    BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence

end Langlands.Plancherel
