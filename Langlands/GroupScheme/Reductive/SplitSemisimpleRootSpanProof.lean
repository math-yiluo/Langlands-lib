import Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanSufficiency
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof

/-! # Semisimplicity is equivalent to finite root index -/

universe u

namespace Langlands.GroupScheme

/-- The root-span semisimplicity criterion, with all global inputs discharged. -/
theorem splitSemisimpleRootSpan : SplitSemisimpleRootSpanStatement.{u} :=
  splitSemisimpleRootSpan_of_finiteRootIndex.{u}
    (splitSemisimpleOfFiniteRootIndex_of_maximalTorusCentralizer.{u}
      maximalTorusCentralizer.{u})

end Langlands.GroupScheme
