import Langlands.Geometry.Building.KPZeroSubgroups
import Langlands.GroupScheme.Reductive.QuasiSplit

/-! # Quasi-splitness over the actual unramified closure -/

universe u

open AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- Every connected reductive group over the maximal unramified extension of a
nonarchimedean local field has a field-defined geometric Borel subgroup. -/
def UnramifiedQuasiSplitStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))),
    IsConnectedReductive H → IsQuasiSplit H

end Langlands.Geometry.Building
