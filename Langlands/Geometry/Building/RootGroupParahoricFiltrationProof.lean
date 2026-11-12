import Langlands.Geometry.Building.AffineIwahoriTitsInputStatements
import Langlands.Geometry.Building.PointParahoricRootIntersection
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.DynamicRootOrderedProductProof

/-! # Proof of `U_a(F) ∩ P_x ⊆ U_{a,x,0}` for the actual parahoric data -/

universe u

open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- **`U_a(F) ∩ P_x ⊆ U_{a,x,0}`** (the consequence of KP Proposition 7.3.12) for the actual
parahoric data under the apartment axioms, every relative root and every apartment point. -/
theorem rootGroupParahoricFiltration : RootGroupParahoricFiltrationStatement.{u} := by
  intro F _ _ _ _ G _ P hP α x
  exact (P.rootGroup_inf_parahoricAt_eq_filtration hP
    (rootRankOneFactorization F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus)
    RelativeRoot.dynamicRootOrderedProduct x α.2).le

end Langlands.Geometry.Building
