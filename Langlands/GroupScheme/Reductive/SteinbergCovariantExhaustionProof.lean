import Langlands.GroupScheme.Reductive.SteinbergBigCellReduction
import Langlands.GroupScheme.Reductive.SteinbergBigCellRootCorootAssembly
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.SimplyConnected.SplitNecessity

/-! # Unconditional covariant exhaustion by Steinberg-type products -/

universe u

namespace Langlands.GroupScheme

/-- Covariant exhaustion with root-datum existence and the coroot-span input discharged. -/
theorem steinbergCovariantExhaustion : SteinbergCovariantExhaustionStatement.{u} :=
  steinbergCovariantExhaustion_of_bigCell.{u}
    (steinbergBigCell_of_rootAndCoroot.{u}
      rootDatumExistence.{u} splitSimplyConnectedCorootSpan.{u})

end Langlands.GroupScheme
