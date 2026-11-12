import Langlands.GroupScheme.Reductive.RootDatumCorootComparison
import Langlands.GroupScheme.Torus.WeylImageFinite

/-! # rootDatumUniqueness: unconditional proof from published reductions -/

universe u

namespace Langlands.GroupScheme

/-- Any two actual root data of a specified split maximal torus in a connected reductive field group admit a reindexing matching both roots and coroots. -/
theorem rootDatumUniqueness :
    RootDatumUniquenessStatement.{u} :=
  rootDatumUniqueness_of_weylImageFinite splitTorusWeylImageFinite

end Langlands.GroupScheme
