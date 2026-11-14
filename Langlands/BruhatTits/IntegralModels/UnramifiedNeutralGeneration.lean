import Langlands.BruhatTits.IntegralModels.IntegralRootCentralizerGeneration
import Langlands.BruhatTits.IntegralModels.UnramifiedOpenGeneration

/-! # Generation of the actual unramified neutral integral points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G)
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (Ω : Set C.Apartment)
    (hN : D.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω))

set_option maxHeartbeats 800000 in
/-- The actual integral centralizer and apartment root fixers generate all
neutral integral points, without a boundedness or finite-index premise. -/
theorem unramifiedNeutralRootCentralizerGroup_eq_neutral :
    unramifiedNeutralRootCentralizerGroup C D Ω hN = D.neutral.integralPoints := by
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).1
  let : Smooth D.neutral.group.X.hom := D.neutral_smooth
  obtain ⟨H, j, hj, _, hH⟩ :=
    RelativeIdentityComponent.smoothExistence _ D.full.group D.full_smooth
  let : GeometricallyConnected H.X.hom := hH
  let : GeometricallyConnected D.neutral.group.X.hom :=
    D.isRelativeComponent.geometricallyConnected hj
  let A : IntegralSplitTorusData D.neutral C.i :=
    unramifiedNeutralSplitTorusData C D Ω hN
  have hgen : D.neutral.rootCentralizerIntegralPoints C.i = D.neutral.integralPoints :=
    A.rootCentralizerIntegralPoints_eq C.isConnectedReductive C.isMaximalSplitTorus
  have hroots : (⨆ a : relativeRoots C.i, D.neutral.integralPoints ⊓ rootGroupPoints C.i a) =
      C.sharpFixer Ω := by
    apply iSup_congr
    intro a
    rw [inf_comm]
    exact rootGroupPoints_inf_unramifiedNeutral_eq_rootFixer C D Ω hN a
  have hcentral := A.centralizerModel_map_integralPoints_eq
    C.centralizer.j C.centralizer.isRepresentedBy
  change (A.centralizerModel C.centralizer.j C.centralizer.isRepresentedBy).integralPoints.map
      (rationalPoints.map C.centralizer.j) ⊔ C.sharpFixer Ω = _
  rw [hcentral, sup_comm]
  rw [IntegralModel.rootCentralizerIntegralPoints, hroots] at hgen
  exact hgen

/-- Identify the generated subgroup with the actual neutral integral-point
group without changing its ambient rational points. -/
def unramifiedNeutralRootCentralizerEquiv :
    unramifiedNeutralRootCentralizerGroup C D Ω hN ≃* D.neutral.integralPoints :=
  MulEquiv.subgroupCongr (unramifiedNeutralRootCentralizerGroup_eq_neutral C D Ω hN)

@[simp]
theorem coe_unramifiedNeutralRootCentralizerEquiv
    (x : unramifiedNeutralRootCentralizerGroup C D Ω hN) :
    (unramifiedNeutralRootCentralizerEquiv C D Ω hN x : rationalPoints G) = x := rfl

end Langlands.BruhatTits.IntegralModels
