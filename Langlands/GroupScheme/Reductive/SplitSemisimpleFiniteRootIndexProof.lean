import Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanSufficiency
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof

/-! # Finite root index implies semisimplicity -/

universe u

namespace Langlands.GroupScheme

/-- The finite-root-index criterion, with the maximal-torus centralizer input discharged. -/
theorem splitSemisimpleOfFiniteRootIndex :
    SplitSemisimpleOfFiniteRootIndexStatement.{u} :=
  splitSemisimpleOfFiniteRootIndex_of_maximalTorusCentralizer.{u}
    maximalTorusCentralizer.{u}

end Langlands.GroupScheme
