import Langlands.BruhatTits.IntegralModels.UnramifiedFacetImageRecovery
import Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelReduction
import Langlands.Geometry.Building.UnramifiedZeroIndependenceProof

/-! # Apartment reduction for actual descended facet models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

private instance facetApartmentReductionAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
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

include hfac in
/-- The restricted-facet identity places the image of each apartment facet
inside one upstairs facet; it also preserves its nonemptiness. -/
theorem exists_facet_containing_apartmentFacet_image
    {Fa : Set B.Apartment} (hFa : AffineRootSystem.IsFacet B.affineRoots Fa) :
    ∃ Ua : Set C.Apartment, AffineRootSystem.IsFacet C.affineRoots Ua ∧
      (a '' Fa).Nonempty ∧ a '' Fa ⊆ Ua := by
  obtain ⟨x, rfl⟩ := hFa
  refine ⟨AffineRootSystem.facet C.affineRoots (a x),
    AffineRootSystem.isFacet_facet _ _, ?_, ?_⟩
  · exact ⟨a x, x, AffineRootSystem.mem_facet_self _ _, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    change y ∈ a ⁻¹' AffineRootSystem.facet C.affineRoots (a x)
    rwa [hfac x]

include hequiv hap in
/-- The image of a translated apartment subset is the corresponding
translated image of its affine apartment image. -/
theorem image_translatedApartmentMap_eq (g : rationalPoints G) (Fa : Set B.Apartment) :
    e '' (B.translatedApartmentMap g '' Fa) =
      (fun x => rationalExtend F (inertiaFixedField F) G g • C.apartmentMap x) ''
        (a '' Fa) := by
  rw [Set.image_image, Set.image_image]
  apply Set.image_congr
  intro x _
  change e (g • B.apartmentMap x) =
    rationalExtend F (inertiaFixedField F) G g • C.apartmentMap (a x)
  rw [hequiv, hap]

include hequiv hap hfac in
/-- For incident downstairs facets and any actual identity-generic comparison
of their characterized upstairs models, one common inner transport places both
models in the chosen upstairs apartment. The containing upstairs facets are
incident in the direction required by the model map. -/
theorem exists_incident_apartment_models
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (Fc Fc' : BuildingFacet B) (hFC : FacetPrecedes B Fc Fc')
    (N N' : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hN : N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val))
    (hN' : N'.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc'.val))
    (ψ : N'.Hom N (𝟙 _)) :
    ∃ (g : rationalPoints G) (Ω Ω' Fa Ca : Set C.Apartment),
      Ω.Nonempty ∧ Ω'.Nonempty ∧
      AffineRootSystem.IsFacet C.affineRoots Fa ∧
      AffineRootSystem.IsFacet C.affineRoots Ca ∧
      AffineRootSystem.IsFaceOf C.affineRoots Fa Ca ∧
      Ω ⊆ Fa ∧ Ω' ⊆ Ca ∧
      e '' Fc.val =
        (fun x => rationalExtend F (inertiaFixedField F) G g • C.apartmentMap x) '' Ω ∧
      e '' Fc'.val =
        (fun x => rationalExtend F (inertiaFixedField F) G g • C.apartmentMap x) '' Ω' ∧
      (N.transport ((baseChanged F (inertiaFixedField F) G).innerIso
        (rationalExtend F (inertiaFixedField F) G g)⁻¹)).integralPoints =
          E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) ∧
      (N'.transport ((baseChanged F (inertiaFixedField F) G).innerIso
        (rationalExtend F (inertiaFixedField F) G g)⁻¹)).integralPoints =
          E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω') := by
  obtain ⟨g, Fa₀, Ca₀, hface, hFc, hFc'⟩ := hFC
  have hCa₀ : AffineRootSystem.IsFacet B.affineRoots Ca₀ := by
    obtain ⟨_, x, hx, _⟩ := hface
    exact ⟨x, hx⟩
  obtain ⟨Fa, hFa, hne, hsub⟩ :=
    exists_facet_containing_apartmentFacet_image B C a hfac hface.1
  obtain ⟨Ca, hCa, hne', hsub'⟩ :=
    exists_facet_containing_apartmentFacet_image B C a hfac hCa₀
  have hY : e '' Fc.val =
      (fun x => rationalExtend F (inertiaFixedField F) G g • C.apartmentMap x) ''
        (a '' Fa₀) := by
    rw [hFc]
    exact image_translatedApartmentMap_eq B C e a hequiv hap g Fa₀
  have hY' : e '' Fc'.val =
      (fun x => rationalExtend F (inertiaFixedField F) G g • C.apartmentMap x) ''
        (a '' Ca₀) := by
    rw [hFc']
    exact image_translatedApartmentMap_eq B C e a hequiv hap g Ca₀
  have hpts := integralPoints_transport_innerIso unramifiedZeroPointsIndependence C E E
    (rationalExtend F (inertiaFixedField F) G g) (a '' Fa₀) N (hN.trans (by rw [hY]))
  have hpts' := integralPoints_transport_innerIso unramifiedZeroPointsIndependence C E E
    (rationalExtend F (inertiaFixedField F) G g) (a '' Ca₀) N' (hN'.trans (by rw [hY']))
  have hle :
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' (a '' Ca₀)) ≤
        E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' (a '' Fa₀)) := by
    rw [← hpts', ← hpts]
    let ψt := ψ.transportId ((baseChanged F (inertiaFixedField F) G).innerIso
      (rationalExtend F (inertiaFixedField F) G g)⁻¹)
    intro q hq
    simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using
      ψt.map_mem_integralPoints hq
  exact ⟨g, a '' Fa₀, a '' Ca₀, Fa, Ca, hne, hne', hFa, hCa,
    E.isFaceOf_of_zeroFixer_le C hCa hFa hne' hsub' hne hsub hle,
    hsub, hsub', hY, hY', hpts, hpts'⟩

include hequiv hap hfac in
/-- A choice of the common original rational translation supplied by
`exists_incident_apartment_models`. Its remaining coordinates and properties
are given by `Classical.choose_spec` of that theorem. -/
def incidentApartmentTranslation
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (Fc Fc' : BuildingFacet B) (hFC : FacetPrecedes B Fc Fc')
    (N N' : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hN : N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val))
    (hN' : N'.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc'.val))
    (ψ : N'.Hom N (𝟙 _)) : rationalPoints G :=
  (exists_incident_apartment_models B C e a hequiv hap hfac E Fc Fc' hFC N N' hN hN' ψ).choose

end Langlands.BruhatTits.IntegralModels
