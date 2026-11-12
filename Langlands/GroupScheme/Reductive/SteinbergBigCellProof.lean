import Langlands.GroupScheme.Reductive.SteinbergBigCellRootCorootAssembly
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.SimplyConnected.SplitNecessity

/-! # Proof of the big-cell and Steinberg data statement -/

universe u

namespace Langlands.GroupScheme

/-- **Big-cell and Steinberg data** for simply connected groups over algebraically closed
fields of prime characteristic. The published root-and-coroot assembly applied to the proved
root-datum existence theorem and the proved integral coroot span of simply connected groups. -/
theorem steinbergBigCell : SteinbergBigCellStatement.{u} :=
  steinbergBigCell_of_rootAndCoroot rootDatumExistence splitSimplyConnectedCorootSpan

end Langlands.GroupScheme
