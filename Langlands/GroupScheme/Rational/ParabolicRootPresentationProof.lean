import Langlands.GroupScheme.Rational.ParabolicRootPresentationDynamicConstruction
import Langlands.GroupScheme.Rational.ParabolicRootPresentationIndependenceReduction
import Langlands.GroupScheme.Rational.RootGeneratedCentralizerReduction
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Existence and full independence of parabolic root presentations: proof -/

universe u

namespace Langlands.GroupScheme

/-- Every specified rational parabolic, rational Levi and split component of a
connected reductive group over any field admits a compatible root presentation. -/
theorem parabolicRootPresentationExistence :
    ParabolicRootPresentationExistenceStatement.{u} :=
  parabolicRootPresentationExistenceStatement_of_dynamic_centralizer
    genericMinimalParabolic relativeRootNegation parabolicDynamic
    dynamicCentralizerReductive

/-- **Existence, full independence and component transport of parabolic root
presentations** (a derived target motivated by Renard 2026 V.3.14–V.3.15). Actual
reflection data come from the published rank-one factorization. -/
theorem parabolicRootPresentation : ParabolicRootPresentationStatement.{u} :=
  parabolicRootPresentationStatement_of_existence_of_reflections
    parabolicRootPresentationExistence
    (relativeRootReflectionExistence_of_rootRankOneFactorization rootRankOneFactorization)

end Langlands.GroupScheme
