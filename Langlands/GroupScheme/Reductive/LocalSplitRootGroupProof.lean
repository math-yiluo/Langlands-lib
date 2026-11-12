import Langlands.GroupScheme.Reductive.LocalSplitReducedIsomorphismReduction
import Langlands.GroupScheme.Reductive.LocalSplitReducedIsomorphismProof

/-! # Root parametrizations over reduced local rings -/

universe u

namespace Langlands.GroupScheme

/-- The exact published proposition, with its structural inputs discharged. -/
theorem localSplitRootGroup :
    LocalSplitRootGroupStatement.{u} :=
  localSplitRootGroup_of_simple localSplitSimpleRootGroup

end Langlands.GroupScheme
