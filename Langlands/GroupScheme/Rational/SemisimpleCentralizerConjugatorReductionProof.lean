import Langlands.GroupScheme.Rational.MaximalTorusConjugatorCaseC
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Rational.MaximalTorusConjugatorCaseCData
import Langlands.GroupScheme.Lie.TorusLieCentralizerProof
import Langlands.GroupScheme.Lie.CharZeroTorusLieCentralizerProof

/-! # The semisimple centralizer conjugator reduction -/

universe u

namespace Langlands.GroupScheme

/-- The semisimple centralizer conjugator reduction, with all structural inputs discharged. -/
theorem semisimpleCentralizerConjugatorReduction : SemisimpleCentralizerConjugatorReductionStatement.{u} :=
  semisimpleCentralizerConjugatorReduction_of_data.{u}
    maximalTorusConjugacy.{u} maximalTorusBaseChange.{u}
    (semisimpleCentralizerConjugationData.{u}
      semisimpleMaximalTorusLieCentralizer.{u} charZeroTorusLieCentralizer.{u}
      maximalTorusBaseChange.{u})

end Langlands.GroupScheme
