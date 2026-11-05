import Langlands.Geometry.Building.UnramifiedZeroComparison
import Langlands.Geometry.Building.UnramifiedTorusNormComparison
import Langlands.Geometry.Building.UnramifiedSharpTorusConjugacyStatement
import Langlands.Geometry.Building.UnramifiedZeroIndependenceStatement

/-! # Independence of zero subgroups conditional on sharp torus conjugacy -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

/-- Sharp conjugacy, together with norm comparison for arbitrary splitting
fields, implies the exact zero-subgroup independence statement. -/
theorem unramifiedZeroPointsIndependence_of_sharpConjugacy
    (h : UnramifiedSharpTorusConjugacyStatement.{u}) :
    UnramifiedZeroPointsIndependenceStatement.{u} := by
  intro F _ _ _ _ H E E'
  obtain ⟨g, hg, e, he⟩ := h F H E.D E.C E.d E.π
    E.isSimplyConnectedDerivedCover E.T E'.T E.i E'.i
    E.isMaximallySplitMaximalTorus E'.isMaximallySplitMaximalTorus
  exact E.zeroPoints_eq_of_sharp_torus_iso E' g hg e he
    (E.torusIwahori_map_eq_of_iso E' e)

namespace UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}

/-- Conditional on sharp conjugacy, the identity on ambient rational points
identifies the zero subgroups defined by any two data. -/
def zeroPointsEquivOfSharpConjugacy
    (h : UnramifiedSharpTorusConjugacyStatement.{u})
    (E E' : UnramifiedZeroDatum F H) : E.zeroPoints ≃* E'.zeroPoints :=
  MulEquiv.subgroupCongr
    (unramifiedZeroPointsIndependence_of_sharpConjugacy h F H E E')

@[simp] theorem zeroPointsEquivOfSharpConjugacy_coe
    (h : UnramifiedSharpTorusConjugacyStatement.{u})
    (E E' : UnramifiedZeroDatum F H) (x : E.zeroPoints) :
    (E.zeroPointsEquivOfSharpConjugacy h E' x : rationalPoints H) = x := rfl

end UnramifiedZeroDatum

end Langlands.Geometry.Building
