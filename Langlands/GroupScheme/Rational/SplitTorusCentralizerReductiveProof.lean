import Langlands.GroupScheme.Rational.SplitTorusCentralizerReduction
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Reductivity of split-torus centralizers -/

universe u

namespace Langlands.GroupScheme

/-- The exact published proposition, with its structural inputs discharged. -/
theorem splitTorusCentralizerReductive :
    SplitTorusCentralizerReductiveStatement.{u} :=
  splitTorusCentralizerReductive_of_dynamic dynamicCentralizerReductive

end Langlands.GroupScheme
