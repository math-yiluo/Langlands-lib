import Langlands.GroupScheme.Rational.ReflectionStandardCocharacter
import Langlands.GroupScheme.Rational.RelativeRootSignsProof
import Langlands.GroupScheme.Rational.RootGeneratedCentralizerReduction
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof

/-! # Proof of standard-cocharacter existence and the dynamic comparison -/

universe u

namespace Langlands.GroupScheme

/-- For a maximal split torus of a connected reductive group over any field and
a generic cocharacter, every subset of the simple relative roots has a standard
cocharacter. For each such cocharacter, the choice-free standard parabolic,
Levi and unipotent subgroup functors equal its dynamic subgroup functors. -/
theorem standardCocharacter : StandardCocharacterStatement.{u} :=
  standardCocharacterStatement_of_reflections_of_signs
    (relativeRootReflectionExistence_of_rootRankOneFactorization rootRankOneFactorization)
    relativeRootSignsDetermineDynamic

end Langlands.GroupScheme
