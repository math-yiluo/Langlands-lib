import Langlands.GroupScheme.Rational.MaximalTorusConjugatorReductionCases
import Langlands.GroupScheme.Rational.MaximalTorusIsogenyReduction
import Langlands.GroupScheme.Rational.MaximalTorusConjugatorCaseC
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Rational.MaximalTorusConjugatorCaseCData
import Langlands.GroupScheme.Lie.TorusLieCentralizerProof
import Langlands.GroupScheme.Lie.CharZeroTorusLieCentralizerProof

/-! # The maximal torus conjugator reduction -/

universe u

namespace Langlands.GroupScheme

/-- The maximal torus conjugator reduction, with all structural inputs discharged. -/
theorem maximalTorusConjugatorReduction : MaximalTorusConjugatorReductionStatement.{u} :=
  maximalTorusConjugatorReduction_of_cases.{u} maximalTorusIsogenyReduction.{u}
    (semisimpleCentralizerConjugatorReduction_of_data.{u}
      maximalTorusConjugacy.{u} maximalTorusBaseChange.{u}
      (semisimpleCentralizerConjugationData.{u}
        semisimpleMaximalTorusLieCentralizer.{u} charZeroTorusLieCentralizer.{u}
        maximalTorusBaseChange.{u}))

end Langlands.GroupScheme
