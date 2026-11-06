import Langlands.GroupScheme.Rational.MaximalTorusParameterUnirationalStatement
import Langlands.GroupScheme.Rational.MaximalTorusConjugatorCaseC
import Langlands.GroupScheme.Rational.MaximalTorusConjugatorCaseCData
import Langlands.GroupScheme.Rational.MaximalTorusIsogenyReduction
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Lie.TorusLieCentralizerProof
import Langlands.GroupScheme.Lie.CharZeroTorusLieCentralizerProof

/-! # Proof: unirationality of the actual maximal-torus parameter scheme -/

universe u

namespace Langlands.GroupScheme

/-- **Unirationality of the scheme of maximal tori.** For a smooth connected affine group `G`
over a field `k` with a maximal torus `j₀`, every actual parameter scheme `Q` of the maximal
tori of `G` is unirational over `k`. -/
theorem maximalTorusParameterUnirational : MaximalTorusParameterUnirationalStatement.{u} :=
  maximalTorusParameterUnirational_of_isogeny_data maximalTorusIsogenyReduction
    maximalTorusConjugacy maximalTorusBaseChange
    (semisimpleCentralizerConjugationData semisimpleMaximalTorusLieCentralizer
      charZeroTorusLieCentralizer maximalTorusBaseChange)

end Langlands.GroupScheme
