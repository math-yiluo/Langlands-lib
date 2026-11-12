import Langlands.GroupScheme.Rational.MaximalTorusConjugatorCaseCData
import Langlands.GroupScheme.Lie.TorusLieCentralizerProof
import Langlands.GroupScheme.Lie.CharZeroTorusLieCentralizerProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof

/-! # Generic semisimple centralizer conjugation data -/

universe u

namespace Langlands.GroupScheme

/-- Generic semisimple centralizer conjugation data, with all structural inputs discharged. -/
theorem semisimpleCentralizerConjugationDataUnconditional : SemisimpleCentralizerConjugationDataStatement.{u} :=
  semisimpleCentralizerConjugationData.{u}
    semisimpleMaximalTorusLieCentralizer.{u} charZeroTorusLieCentralizer.{u}
    maximalTorusBaseChange.{u}

end Langlands.GroupScheme
