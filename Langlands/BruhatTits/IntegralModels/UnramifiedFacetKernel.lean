import Langlands.BruhatTits.IntegralModels.UnramifiedSpecialFibreKernel
import Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelStatement
import Langlands.BruhatTits.IntegralModels.FacetParabolicOrder
import Langlands.Geometry.Building.FacetClosurePullback
import Langlands.Geometry.Building.IntegerValuationChamberBounded
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.LeftRightNhds

/-! # Full kernels for characterized descended incident facet models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter Topology
open scoped ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

private theorem image_facetClosure_subset_initialClosure
    {V P W Q : Type*}
    [AddCommGroup V] [Module ℝ V] [AddTorsor V P]
    [AddCommGroup W] [Module ℝ W] [AddTorsor W Q]
    (Ψ : Set (P →ᵃ[ℝ] ℝ)) (a : P →ᵃ[ℝ] Q) (p : P) :
    a '' AffineRootSystem.facetClosure Ψ p ⊆
      @closure Q
        (⨅ f : Q →ᵃ[ℝ] ℝ, TopologicalSpace.induced f inferInstance)
        (a '' AffineRootSystem.facet Ψ p) := by
  let : TopologicalSpace Q :=
    ⨅ f : Q →ᵃ[ℝ] ℝ, TopologicalSpace.induced f inferInstance
  rintro _ ⟨q, hq, rfl⟩
  let c : ℝ → Q := fun t => a (AffineMap.lineMap q p t)
  have hc : Continuous c := by
    apply continuous_iInf_rng.mpr
    intro f
    apply continuous_induced_rng.mpr
    change Continuous (fun t : ℝ => f (a (AffineMap.lineMap q p t)))
    simp only [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module]
    fun_prop
  have hlim : Tendsto c (𝓝[>] 0) (𝓝 (a q)) := by
    simpa only [c, AffineMap.lineMap_apply_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  exact ⟨AffineMap.lineMap q p t,
    AffineRootSystem.lineMap_mem_facet_of_mem_facetClosure hq ht.1 ht.2.le, rfl⟩

private instance facetKernelAffineHom {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- A common actual apartment chart for the images of two incident downstairs
facets, with precisely the geometric hypotheses of the full-kernel statement. -/
structure IncidentFacetKernelChart
    (B : ValuationBuildingData G)
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (e : B.ReducedBuilding → C.ReducedBuilding)
    (Fc Fc' : BuildingFacet B) where
  translation : rationalPoints G
  lower : Set C.Apartment
  upper : Set C.Apartment
  lower_nonempty : lower.Nonempty
  upper_bounded : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' upper)
  lower_subset_closure : lower ⊆ @closure C.Apartment
    (⨅ f : C.Apartment →ᵃ[ℝ] ℝ, TopologicalSpace.induced f inferInstance) upper
  lower_image : e '' Fc.val =
    (fun x => rationalExtend F (inertiaFixedField F) G translation • C.apartmentMap x) ''
      lower
  upper_image : e '' Fc'.val =
    (fun x => rationalExtend F (inertiaFixedField F) G translation • C.apartmentMap x) ''
      upper

variable
    (B : ValuationBuildingData G)
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (e : B.ReducedBuilding → C.ReducedBuilding)
    (a : B.Apartment →ᵃ[ℝ] C.Apartment)
    (hequiv : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
      e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
    (hap : ∀ x : B.Apartment, e (B.apartmentMap x) = C.apartmentMap (a x))
    (hfac : ∀ x : B.Apartment,
      a ⁻¹' AffineRootSystem.facet C.affineRoots (a x) =
        AffineRootSystem.facet B.affineRoots x)

include hequiv hap hfac in
private theorem incidentFacetKernelChart_nonempty
    (Fc Fc' : BuildingFacet B) (hFC : FacetPrecedes B Fc Fc') :
    Nonempty (IncidentFacetKernelChart B C e Fc Fc') := by
  obtain ⟨g, Fa, Ca, hface, hFc, hFc'⟩ := hFC
  obtain ⟨x, hx, hsub⟩ := hface.2
  have hupper : a '' Ca ⊆ AffineRootSystem.facet C.affineRoots (a x) := by
    rintro _ ⟨y, hy, rfl⟩
    change y ∈ a ⁻¹' AffineRootSystem.facet C.affineRoots (a x)
    rw [hfac x]
    rwa [hx]
  have hcl : a '' Fa ⊆ @closure C.Apartment
      (⨅ f : C.Apartment →ᵃ[ℝ] ℝ, TopologicalSpace.induced f inferInstance)
        (a '' Ca) := by
    rw [← hx]
    exact (Set.image_mono hsub).trans
      (image_facetClosure_subset_initialClosure B.affineRoots a x)
  have hne : (a '' Fa).Nonempty := by
    obtain ⟨y, hy⟩ := hface.1
    rw [← hy]
    exact ⟨a y, y, AffineRootSystem.mem_facet_self _ _, rfl⟩
  refine ⟨{
    translation := g
    lower := a '' Fa
    upper := a '' Ca
    lower_nonempty := hne
    upper_bounded := fun f =>
      (C.isBoundedApartmentSubset_facet (MaximalUnramified.exists_order_ne_zero F)
        (a x) f).mono (Set.image_mono hupper)
    lower_subset_closure := hcl
    lower_image := ?_
    upper_image := ?_ }⟩
  · rw [hFc, Set.image_image, Set.image_image]
    apply Set.image_congr
    intro y _
    change e (g • B.apartmentMap y) =
      rationalExtend F (inertiaFixedField F) G g • C.apartmentMap (a y)
    rw [hequiv, hap]
  · rw [hFc', Set.image_image, Set.image_image]
    apply Set.image_congr
    intro y _
    change e (g • B.apartmentMap y) =
      rationalExtend F (inertiaFixedField F) G g • C.apartmentMap (a y)
    rw [hequiv, hap]

include hequiv hap hfac in
/-- Choose the common chart with bounded upper subset and ordinary affine
closure incidence, using only the three indicated apartment-descent hypotheses. -/
def incidentFacetKernelChart
    (Fc Fc' : BuildingFacet B) (hFC : FacetPrecedes B Fc Fc') :
    IncidentFacetKernelChart B C e Fc Fc' :=
  Classical.choice
    (incidentFacetKernelChart_nonempty B C e a hequiv hap hfac Fc Fc' hFC)

local instance facetKernelIntegerAlgebra :
    Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance facetKernelIntegerScalarTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance facetKernelIntegerLocalHom :
    IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  Valuation.HasExtension.instIsLocalHomValuationInteger
    (vR := ValuativeRel.valuation F) (vS := fixedFieldValuation F)

include hequiv hap hfac in
/-- The full unramified model-kernel statement gives the full neutral
special-fibre kernel for any characterized pair of incident descended facets.
No additional boundedness or closure premise is required. -/
theorem unramifiedFacetKernel_of_modelKernel
    (hkernel : UnramifiedModelKernelStatement.{u})
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (Fc Fc' : BuildingFacet B) (hFC : FacetPrecedes B Fc Fc')
    (D D' : RelativeComponentModelData ↥𝒪[F] F G)
    (hD : D.neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val))
    (hD' : D'.neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc'.val))
    (φ : RelativeComponentModelHom D' D) :
    φ.HasSmoothConnectedUnipotentKernel := by
  let J := incidentFacetKernelChart B C e a hequiv hap hfac Fc Fc' hFC
  have htarget : D.neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer
        ((fun x => rationalExtend F (inertiaFixedField F) G J.translation •
          C.apartmentMap x) '' J.lower) := by
    rw [hD, J.lower_image]
  have hsource : D'.neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer
        ((fun x => rationalExtend F (inertiaFixedField F) G J.translation •
          C.apartmentMap x) '' J.upper) := by
    rw [hD', J.upper_image]
  have hψ := hkernel F G C E
    (rationalExtend F (inertiaFixedField F) G J.translation) J.lower J.upper
    J.lower_nonempty J.upper_bounded J.lower_subset_closure
    D.neutral.baseChangeUnramified D'.neutral.baseChangeUnramified
    (D.neutral.isSmooth_baseChange (fixedFieldIntegers F) (inertiaFixedField F)
      D.neutral_smooth)
    (D'.neutral.isSmooth_baseChange (fixedFieldIntegers F) (inertiaFixedField F)
      D'.neutral_smooth)
    htarget hsource φ.neutral.baseChangeUnramifiedId
  exact φ.neutral.specialFibreKernel_properties_of_baseChange
    (fixedFieldIntegers F) (inertiaFixedField F) hψ

end Langlands.BruhatTits.IntegralModels
