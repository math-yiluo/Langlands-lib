import Langlands.Geometry.Building.KPUnramifiedComparisonZeroDescent
import Langlands.Geometry.Building.UnramifiedMoyPrasadZeroFixerComparison
import Langlands.Geometry.Building.KPZeroDatumExistence
import Langlands.Geometry.Building.UnramifiedZeroFixerSharpComparisonProof

/-! # Assembly of the concrete unramified depth-zero comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.Geometry.Building

private instance unramifiedComparisonZeroProofAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (UnramifiedClosure F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (UnramifiedClosure F)))
  infer_instance

/-- The norm-defined depth-zero group restricts along every supplied apartment
lift to the actual downstairs centralizer-zero subgroup. -/
theorem unramifiedComparisonZeroField :
    UnramifiedComparisonZeroFieldStatement.{u} := by
  intro F _ _ _ _ G _ P _ t L y
  let E := UnramifiedZeroDatum.ofConnectedReductive
    (baseChanged F (UnramifiedClosure F) G) L.buildingData.isConnectedReductive
  rw [← E.zeroPoints_inf_fixer_eq_moyPrasad_of_sharpComparison
    L.buildingData unramifiedZeroFixerSharpComparison L.centralizer_isTorus (L.e y)]
  exact L.comap_zeroPoints_inf_fixer E y

end Langlands.Geometry.Building
