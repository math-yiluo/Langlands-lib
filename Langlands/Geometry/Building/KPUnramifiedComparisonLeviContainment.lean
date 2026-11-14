import Langlands.Geometry.Building.KPUnramifiedComparisonFieldStatements
import Langlands.Geometry.Building.QuasiSplitApartmentShifts
import Langlands.Geometry.Building.CentralizerDatumBaseChange
import Langlands.GroupScheme.Rational.CocharacterCentralizerRootGeneration
import Langlands.GroupScheme.Rational.ScalarExtensionNaturality

/-! # Centralizer containment for integral descended vectors -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance leviContainmentAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (UnramifiedClosure F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (UnramifiedClosure F)))
  infer_instance

namespace ParahoricBuildingData.UnramifiedComparisonTorus.ApartmentLift

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {P : ParahoricBuildingData G} {t : P.UnramifiedComparisonTorus}
    (L : t.ApartmentLift)

set_option maxHeartbeats 1000000 in
/-- Every downstairs centralizer point lies in the upstairs pairing Levi
for the image of any integral downstairs cocharacter. -/
theorem centralizer_mem_pairingLeviSpan_descent_tmul
    (lam : cocharacterLattice P.S) (z : rationalPoints P.centralizer.Z) :
    rationalExtend F (UnramifiedClosure F) G (rationalPoints.map P.centralizer.j z) ∈
      L.buildingData.pairingLeviSpan
        (descentCocharacterMap F (UnramifiedClosure F) t.f
          P.isMaximalSplitTorus.isSplitSubtorus.1 ((1 : ℝ) ⊗ₜ[ℤ] lam)) := by
  let b := algebraBaseMap F (UnramifiedClosure F)
  let lamK := cocharacterLattice.baseChange b P.S lam
  let fK := (CommGroupScheme.baseChange b).map t.f
  let ζ : cocharacterLattice L.buildingData.S := lamK ≫ fK
  let ν : V L.buildingData.S := (1 : ℝ) ⊗ₜ[ℤ] ζ
  change _ ∈ L.buildingData.pairingLeviSpan ν
  apply dynamicCentralizer_rationalPoints_le_of_zeroRootGroups L.buildingData.i
    L.buildingData.isConnectedReductive L.buildingData.isMaximalSplitTorus ζ
    (L.buildingData.pairingLeviSpan ν)
  · intro g hg
    apply Subgroup.mem_sup_left
    rw [← torusCentralizer_carrier_base, ← L.centralizer.isRepresentedBy.2] at hg
    exact hg
  · intro α hα hzero g hg
    apply Subgroup.mem_sup_right
    have hαzero : α ∈ L.buildingData.zeroPairingRoots ν := by
      refine ⟨hα, ?_⟩
      simp only [ν, eval_tmul, hzero, Int.cast_zero, mul_zero]
    exact (show L.buildingData.rootGroup α ≤
      L.buildingData.rootGroupSpan (L.buildingData.zeroPairingRoots ν) from
        le_iSup_of_le α (le_iSup_of_le hαzero le_rfl)) hg
  · have hζ : CommGroupScheme.groupHom ζ ≫ L.buildingData.i =
        CommGroupScheme.groupHom lamK ≫ (GroupScheme.baseChange b).map P.i := by
      change (CommGroupScheme.groupHom lamK ≫ CommGroupScheme.groupHom fK) ≫
        (GroupScheme.baseChange b).map t.iT = _
      rw [Category.assoc]
      change CommGroupScheme.groupHom lamK ≫
        ((GroupScheme.baseChange b).map (CommGroupScheme.groupHom t.f) ≫
          (GroupScheme.baseChange b).map t.iT) = _
      rw [← Functor.map_comp, t.factor]
    rw [hζ, rationalExtend_map]
    apply torusCentralizer_le_dynamicCentralizer
      ((GroupScheme.baseChange b).map P.i) (CommGroupScheme.groupHom lamK) _
    exact centralizerPoints_le_torusCentralizer _
      (map_mem_centralizerPoints (P.centralizer.isRepresentedBy_baseChange (K := UnramifiedClosure F))
        (rationalExtend F (UnramifiedClosure F) P.centralizer.Z z))

end ParahoricBuildingData.UnramifiedComparisonTorus.ApartmentLift

end Langlands.Geometry.Building
