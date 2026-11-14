import Langlands.Geometry.Building.KPUnramifiedComparisonFieldStatements
import Langlands.Geometry.Building.UnramifiedZeroCentralizer
import Langlands.Geometry.Building.NormalizerNormOneFixerBoundedness
import Langlands.Geometry.Building.MaximalUnramifiedApartmentInjective

/-! # Descent of zero point fixers along a concrete apartment lift -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance unramifiedComparisonZeroDescentAffineHom {F : Type u} [Field F]
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

/-- The restriction identity makes every supplied apartment lift injective. -/
theorem e_injective : Function.Injective L.e := by
  intro y y' h
  apply KPApartmentData.Apartment.ext
  rw [L.restrict y, L.restrict y', h]

/-- The supplied lift, viewed as an embedding using its restriction identity. -/
def eEmbedding : P.Apartment ↪ L.apartment.Apartment where
  toFun := L.e
  inj' := L.e_injective

/-- The lift reflects fixation by a downstairs normalizer element. -/
theorem normalizer_smul_eq_iff (n : normalizerPoints P.i) (y : P.Apartment) :
    rationalExtend F (UnramifiedClosure F) G (n : rationalPoints G) •
        L.buildingData.apartmentMap (L.e y) =
      L.buildingData.apartmentMap (L.e y) ↔ n • y = y := by
  rw [← L.normalizer n y]
  exact (maximalUnramifiedApartmentInjective F _ L.buildingData).eq_iff.trans
    L.eEmbedding.injective.eq_iff

/-- The upstairs canonical zero subgroup intersected with the point fixer
restricts to the actual downstairs centralizer-zero subgroup. -/
theorem comap_zeroPoints_inf_fixer
    (E : UnramifiedZeroDatum F (baseChanged F (UnramifiedClosure F) G))
    (y : P.Apartment) :
    ((E.zeroPoints ⊓ L.buildingData.fixer
        (L.buildingData.apartmentMap (L.e y))).comap
      (rationalExtend F (UnramifiedClosure F) G)).comap
        (rationalPoints.map P.centralizer.j) = P.centralizerZero := by
  apply le_antisymm
  · intro z hz
    change rationalExtend F (UnramifiedClosure F) G
      (rationalPoints.map P.centralizer.j z) ∈ E.zeroPoints ⊓
        L.buildingData.fixer (L.buildingData.apartmentMap (L.e y)) at hz
    have hzG : rationalPoints.map P.centralizer.j z ∈
        Plancherel.rationalCommonNormKernel G := by
      rw [← characterValuationKernelDescent_proof F G]
      exact E.zeroPoints_le_characterValuationKernel hz.1
    have hzy : P.centralizer.toNormalizer z • y = y :=
      (L.normalizer_smul_eq_iff (P.centralizer.toNormalizer z) y).mp hz.2
    have hzZ := P.toValuationBuildingData.mem_rationalCommonNormKernel_of_smul_eq z hzG hzy
    change z ∈ P.zeroDatum.centralizerZero
    rw [← P.zeroDatum.comap_unramifiedZeroPoints_inf_centralizerNormKernel E]
    exact ⟨hz.1, hzZ⟩
  · intro z hz
    have hzZ := P.zeroDatum.centralizerZero_le_rationalCommonNormKernel hz
    have hzG := P.zeroDatum.zeroSubgroup_le_comap_unramifiedZeroPoints E
      (P.zeroDatum.map_centralizerZero_le_zeroSubgroup ⟨z, hz, rfl⟩)
    exact ⟨hzG,
      (L.normalizer_smul_eq_iff (P.centralizer.toNormalizer z) y).mpr
        (P.isOmegaCompatible.smul_eq_self hzZ y)⟩

end ParahoricBuildingData.UnramifiedComparisonTorus.ApartmentLift

end Langlands.Geometry.Building
