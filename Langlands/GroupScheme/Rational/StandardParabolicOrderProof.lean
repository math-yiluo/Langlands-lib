import Langlands.GroupScheme.Rational.StandardParabolicOrderStatement
import Langlands.GroupScheme.Rational.StandardParabolicOrderFromRoots
import Langlands.GroupScheme.Rational.ReflectionStandardCocharacter
import Langlands.GroupScheme.Rational.RootGeneratedCentralizerReduction
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.RelativeRootSignsProof
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof

/-! # Proof of the order on standard parabolics -/

universe u

namespace Langlands.GroupScheme

/-- For a maximal split torus of a connected reductive group over any field and
a generic cocharacter, inclusion of subsets of the simple relative roots is
equivalent to inclusion of their standard parabolic subgroup functors. Such an
inclusion gives the covariant Levi and contravariant unipotent inclusions, and
the subset-to-parabolic map is injective. -/
theorem standardParabolicOrder : StandardParabolicOrderStatement.{u} := by
  have hStandard : StandardCocharacterStatement.{u} :=
    standardCocharacterStatement_of_reflections_of_signs
      (relativeRootReflectionExistence_of_rootRankOneFactorization rootRankOneFactorization)
      relativeRootSignsDetermineDynamic
  intro k _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν
  exact standardParabolic_order_of_root_comparison i ν hν
    (relativeRootNegation k G hG T i hi)
    (fun J hJ => (hStandard k G hG T i hi ν hν J hJ).1)
    (fun zeta eta => (relativeRootSignInclusions k G hG T i hi zeta eta).1)
    (fun zeta eta => (relativeRootSignInclusions k G hG T i hi zeta eta).2)

end Langlands.GroupScheme
