import Langlands.BruhatTits.RationalPoints.SmoothRealStructureStatement
import Langlands.BruhatTits.RationalPoints.DerivedSmoothRealReduction
import Langlands.GroupScheme.Rational.PositivePowerFactorizationProof
import Langlands.GroupScheme.Rational.RootGeneratedCentralizerReduction
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof

/-! # Ambient smooth real homomorphisms annihilate algebraic derived rational points

Proof of `DerivedSmoothRealAnnihilationStatement`. The published conditional reduction
`derivedSmoothRealAnnihilation_of_structure` has two proposition premises. The published
`positivePowerTorusAdditiveFactorization` proves the first. The published
`rootRankOneFactorization`, passed through the published adapter
`relativeRootReflectionExistence_of_rootRankOneFactorization`, proves the second. -/

universe u

open Langlands.GroupScheme

namespace Langlands.BruhatTits.RationalPoints

/-- **Derived-point annihilation.** For every nonarchimedean local field `F` and every
connected reductive group `M` over `F`, every group homomorphism from the rational points
to `Multiplicative ℝ` whose kernel is open in the canonical rational-point topology kills
all rational points of the scheme-theoretic derived subgroup. -/
theorem derivedSmoothRealAnnihilation : DerivedSmoothRealAnnihilationStatement.{u} :=
  derivedSmoothRealAnnihilation_of_structure positivePowerTorusAdditiveFactorization.{u}
    (relativeRootReflectionExistence_of_rootRankOneFactorization rootRankOneFactorization.{u})

end Langlands.BruhatTits.RationalPoints
