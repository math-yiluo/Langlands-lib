import Langlands.GroupScheme.Rational.RootGeneratedCentralizerReduction
import Langlands.GroupScheme.Rational.RootSystemFromFactorPairs
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof

/-! # Proof that the actual relative Weyl group is a finite Coxeter group -/

universe u

namespace Langlands.GroupScheme

/-- **The relative Weyl group is a finite Coxeter group**, over arbitrary fields. For a
maximal split torus of a connected reductive group and a generic cocharacter, the actual
group `N(k)/Z(k)` carries a Coxeter system labelled by the actual simple relative roots
that realizes the relative root action. The published rank-one factorization theorem
supplies both the relative root system and the kernel-centralizing reflection data. -/
theorem relativeWeylCoxeter : RelativeWeylCoxeterStatement.{u} :=
  RootGeneratedCentralizerStructuralPremises.relativeWeylCoxeter
    ⟨relativeRootSystemStatement_of_rootRankOneFactorizationStatement rootRankOneFactorization,
      rootRankOneFactorization⟩

end Langlands.GroupScheme
