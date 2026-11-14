import Langlands.BruhatTits.IntegralModels.UnramifiedFacetReflections
import Langlands.Geometry.Building.GenericRootFixerIntersection

/-! # Actual root-point intersections of descended facet models -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- Actual integral sections with generic point in a conjugated root group. -/
def facetRootIntegralSections (g : rationalPoints G)
    (D : RelativeComponentModelData ↥𝒪[F] F G) (a : characterLattice P.S) :
    Subgroup D.neutral.integralSections :=
  (rootGroupPoints (P.i ≫ (G.innerIso g).hom) a).comap D.neutral.integralPointMap

private instance extensionAffineHom :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

variable
  (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
  (e : P.ReducedBuilding → C.ReducedBuilding) (hinj : Function.Injective e)
  (he : ∀ (g : rationalPoints G) (z : P.ReducedBuilding),
    e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
  (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
  (g : rationalPoints G) (Fa : Set P.Apartment)
  (D : RelativeComponentModelData ↥𝒪[F] F G)
  (hD : D.neutral.baseChangeUnramified.integralPoints =
    E.zeroPoints ⊓ C.pointwiseFixer
      (e '' (P.translatedApartmentMap g '' Fa)))
  (hA : P.SatisfiesApartmentAxioms)

include he hD hA

/-- Every conjugated actual root point fixing the apartment subset is integral
in any model with the specified descended zero-fixer characterization. -/
theorem conjugated_rootPoint_mem_integralPoints_of_fixing
    {a : relativeRoots P.i} {x : rationalPoints G}
    (hx : x ∈ P.rootGroup a)
    (hfix : ∀ y ∈ Fa, x • P.apartmentMap y = P.apartmentMap y) :
    rationalPoints.map (G.innerIso g).hom x ∈ D.neutral.integralPoints := by
  apply (D.neutral.mem_integralPoints_rationalExtend_iff_unramified _).mp
  rw [hD]
  constructor
  · apply rationalExtend_mem_zeroPoints_of_mem_simplyConnectedImage P E
    exact map_simplyConnectedImage_le P.zeroDatum.isSimplyConnectedDerivedCover
      P.zeroDatum.isSimplyConnectedDerivedCover (G.innerIso g)
        ⟨x, P.rootGroup_le_simplyConnectedImage hA a a.property hx, rfl⟩
  · apply C.apartment.mem_pointwiseFixer.mpr
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [← he]
    apply congrArg e
    change (x ≫ (G.innerIso g).hom.hom.hom) •
      (g • P.apartmentMap y) = g • P.apartmentMap y
    rw [comp_innerIso_hom, constantPoint_self, mul_smul, mul_smul,
      inv_smul_smul, hfix y hy]

include hinj

/-- For a root point, descended integral membership is exactly the intrinsic
root-fixer condition on the original apartment coordinates. -/
theorem conjugated_rootPoint_mem_integralPoints_iff
    {a : relativeRoots P.i} {x : rationalPoints G} (hx : x ∈ P.rootGroup a) :
    rationalPoints.map (G.innerIso g).hom x ∈ D.neutral.integralPoints ↔
      x ∈ P.apartment.rootFixer a Fa := by
  constructor
  · intro hint
    refine P.apartment.mem_rootFixer.mpr ⟨hx, fun y hy => ?_⟩
    apply P.apartment.mem_filtration_of_mem_rootGroup_of_fixing_apartmentMap
      P.isConnectedReductive P.isMaximalSplitTorus y a.property hx
    have hxK := (D.neutral.mem_integralPoints_rationalExtend_iff_unramified _).mpr hint
    rw [hD] at hxK
    have hfix := C.apartment.mem_pointwiseFixer.mp hxK.2
      (e (P.translatedApartmentMap g y)) ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [← he] at hfix
    have hfixF := hinj hfix
    change (x ≫ (G.innerIso g).hom.hom.hom) •
      (g • P.apartmentMap y) = g • P.apartmentMap y at hfixF
    rw [comp_innerIso_hom, constantPoint_self, mul_smul, mul_smul,
      inv_smul_smul] at hfixF
    exact MulAction.injective g hfixF
  · intro hxF
    apply conjugated_rootPoint_mem_integralPoints_of_fixing P C e he E g Fa D hD hA hx
    intro y hy
    obtain ⟨_, hdepth⟩ := P.apartment.mem_rootFixer.mp hxF
    exact P.apartment.mem_reducedFixer.mp
      ((P.apartment.sharpFixer_le_reducedFixer y)
        ((P.apartment.filtration_le_sharpFixer y a.property) (hdepth y hy)))

/-- The full generic-root intersection with the pullback of the integral-point
subgroup is the actual root fixer, without a boundedness or nonemptiness premise. -/
theorem rootGroupPoints_inf_conjugatedIntegralPoints_eq_rootFixer
    (a : relativeRoots P.i) :
    rootGroupPoints P.i a ⊓ D.neutral.integralPoints.comap
        (rationalPoints.map (G.innerIso g).hom) = P.apartment.rootFixer a Fa := by
  ext x
  constructor
  · intro hx
    exact (conjugated_rootPoint_mem_integralPoints_iff P C e hinj he E g Fa D hD
      hA hx.1).mp hx.2
  · intro hx
    have hxroot := (P.apartment.mem_rootFixer.mp hx).1
    exact ⟨hxroot, (conjugated_rootPoint_mem_integralPoints_iff P C e hinj he E g Fa D
      hD hA hxroot).mpr hx⟩

omit hinj in
/-- A whole affine depth group is integral after conjugation whenever its
functional is nonnegative on the apartment subset. -/
theorem conjugated_affineRootGroup_le_integralPoints
    {a : relativeRoots P.i} {ψ : P.Apartment →ᵃ[ℝ] ℝ}
    (hlin : ψ.linear = rootForm P.i a) (hnonneg : ∀ y ∈ Fa, 0 ≤ ψ y) :
    (P.affineRootGroup a ψ).map (rationalPoints.map (G.innerIso g).hom) ≤
      D.neutral.integralPoints := by
  rintro _ ⟨x, hx, rfl⟩
  have hxroot := P.apartment.affineRootGroup_le_rootGroupPoints a ψ hx
  apply conjugated_rootPoint_mem_integralPoints_of_fixing P C e he E g Fa D hD hA hxroot
  intro y hy
  have hxdepth : x ∈ P.apartment.filtration y a 0 := by
    obtain ⟨_, hv⟩ := (P.apartment.mem_affineRootGroup_iff hlin y).mp hx
    exact ⟨hxroot, (WithTop.coe_le_coe.mpr (hnonneg y hy)).trans hv⟩
  exact P.apartment.mem_reducedFixer.mp
    ((P.apartment.sharpFixer_le_reducedFixer y)
      ((P.apartment.filtration_le_sharpFixer y a.property) hxdepth))

end Langlands.BruhatTits.IntegralModels
