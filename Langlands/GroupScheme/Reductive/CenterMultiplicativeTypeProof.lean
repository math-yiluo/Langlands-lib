import Langlands.GroupScheme.Reductive.CenterMultiplicativeTypeReduction
import Langlands.GroupScheme.Absolute.AlgClosedMaximalTorusCentralizerAssembly
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Torus.NoTorusUnipotent
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof

/-! # centerMultiplicativeType: unconditional proof from published reductions -/

universe u

namespace Langlands.GroupScheme

/-- Every actual full scheme-theoretic center of a connected reductive field group is of multiplicative type, including nonreduced or disconnected centers. -/
theorem centerMultiplicativeType :
    CenterMultiplicativeTypeStatement.{u} :=
  centerMultiplicativeTypeCentralizerReduction
    (algClosedMaximalTorusCentralizerReduction dynamicCentralizerReductive
      noTorusUnipotent solvableTorusQuotient)

end Langlands.GroupScheme
