import Langlands.BruhatTits.SpecialCompact.ParahoricStatement
import Langlands.BruhatTits.SpecialCompact.LeviCompactAlgebraicInclusion
import Langlands.Geometry.Building.KPParahoricFixerComparison

/-! # The point parahoric lies in the norm-one point stabilizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.SpecialCompact

/-- `P_x = j(Z(F)^0) ⊔ G(F)^♯_x ≤ G(F)^1 ∩ G(F)_x` for every apartment point, with no
valuation-topology (V 7) or apartment-axiom premise. -/
theorem parahoricLeCompactStabilizer : ParahoricLeCompactStabilizer.{u} := by
  intro F _ _ _ _ G _ P x
  have hS : IsSplitTorus P.S.toGrp := P.isMaximalSplitTorus.isSplitSubtorus.1
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  refine sup_le (P.map_centralizerZero_le_compactStabilizer x) ?_
  exact le_inf (P.apartment.sharpFixer_le_normKernel_of_split hS P.i x)
    (P.toValuationBuildingData.sharpFixer_le_fixer x)

end Langlands.BruhatTits.SpecialCompact
