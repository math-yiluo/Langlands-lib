import Langlands.Geometry.Building.UnramifiedTwistedChamberStatement
import Langlands.Geometry.Building.UnramifiedTwistedFixedPointStatement
import Langlands.Geometry.Building.UnramifiedTwistedChamberThroughFixedPointStatement

/-! # Assembly of twisted-stable chambers -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- The two remaining geometric inputs suffice for the exact chamber statement. -/
def UnramifiedTwistedChamberReductionStatement : Prop :=
  UnramifiedBuildingMetricStatement.{u} →
    UnramifiedTwistedChamberThroughFixedPointStatement.{u} →
      UnramifiedTwistedChamberStatement.{u}

private instance unramifiedTwistedChamberProofAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

set_option maxHeartbeats 1600000 in
/-- Fixed-point existence and the residual chamber step imply the exact chamber target. -/
theorem unramifiedTwistedChamber_of_fixedPoint
    (hfixed : UnramifiedTwistedFixedPointStatement.{u})
    (hthrough : UnramifiedTwistedChamberThroughFixedPointStatement.{u}) :
    UnramifiedTwistedChamberStatement.{u} := by
  intro F _ _ _ _ G hG T iT
  let _ : IsAffineHom G.X.hom := hG.isAffineHom
  intro hiT
  let _ := mono_of_isMaximalSplitTorus hiT
  let _ : Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro D C h6 hD c hc hfin
  obtain ⟨y, hy⟩ := hfixed F G hG T iT hiT D C h6 hD c hc hfin
  obtain ⟨Y, hY, hstable, _⟩ := hthrough F G hG T iT hiT D C h6 hD c hc hfin y hy
  exact ⟨Y, hY, hstable⟩

/-- The metric existence and residual chamber statements are the remaining inputs. -/
theorem unramifiedTwistedChamber_of_metric
    (hmetric : UnramifiedBuildingMetricStatement.{u})
    (hthrough : UnramifiedTwistedChamberThroughFixedPointStatement.{u}) :
    UnramifiedTwistedChamberStatement.{u} :=
  unramifiedTwistedChamber_of_fixedPoint
    (unramifiedTwistedFixedPoint_of_metric hmetric) hthrough

/-- The conditional chamber reduction holds at arbitrary universe. -/
theorem unramifiedTwistedChamberReduction :
    UnramifiedTwistedChamberReductionStatement.{u} :=
  unramifiedTwistedChamber_of_metric

end Langlands.Geometry.Building
