import Langlands.BruhatTits.IntegralModels.UnramifiedResidueConjugateAttainment
import Langlands.Geometry.Building.BuildingFacetAction
import Langlands.GroupScheme.IntegralModel.UnramifiedSmoothHomExtensionProof
import Langlands.GroupScheme.IntegralModel.GenericRigidity
import Langlands.GroupScheme.IntegralModel.SmoothIntersection
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent

/-! # Conjugation covariance of actual descended facet models -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building Langlands.LocalGalois.Separable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)

/-- The inner automorphism of an integral section extends its generic inner automorphism. -/
def innerHom (s : M.integralSections) :
    M.Hom M (G.innerIso (M.integralPointMap s)).hom where
  hom := (M.group.innerIso s).hom
  generic_comm := by
    rw [baseChange_innerIso_hom, innerIso_hom_comp]
    rfl

/-- Reduction of the actual model inner automorphism is inner conjugation by the reduction. -/
theorem innerHom_specialFibreMap [IsLocalRing R] (s : M.integralSections) :
    (M.innerHom s).specialFibreMap = (M.specialFibre.innerIso (M.reduction s)).hom := by
  exact baseChange_innerIso_hom (residueBaseMap R) s

end Langlands.GroupScheme.IntegralModel

namespace Langlands.BruhatTits.IntegralModels.FacetModelData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)
  (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
  (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
  (e : B.ReducedBuilding → C.ReducedBuilding)
  (hequiv : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
    e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
  (M : FacetModelData B ↥𝒪[F])
  (hmodel : ∀ Fc : BuildingFacet B,
    (M.model Fc).neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val))

private instance facetConjugation_affine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

include hequiv hmodel in
/-- Generic conjugation extends between the actual models of translated facets. -/
theorem exists_neutralConjugationHom (g : rationalPoints G) (Fc : BuildingFacet B) :
    Nonempty ((M.model Fc).neutral.Hom
      (M.model (B.facetTranslateEquiv g Fc)).neutral (G.innerIso g).hom) := by
  apply IntegralModel.unramifiedSmoothHomExtension F G G (G.innerIso g).hom
    (M.model Fc).neutral (M.model (B.facetTranslateEquiv g Fc)).neutral
    (M.model Fc).neutral_smooth
  intro z hz
  rw [hmodel] at hz ⊢
  rw [baseChange_innerIso_hom, ← rationalExtend_eq_baseChangeBasePoint,
    rationalPoints_map_innerIso]
  refine ⟨E.normal_zeroPoints.conj_mem z hz.1
    (rationalExtend F (inertiaFixedField F) G g), ?_⟩
  apply C.apartment.mem_pointwiseFixer.mpr
  rintro y ⟨w, hw, rfl⟩
  change w ∈ (fun x => g • x) '' Fc.val at hw
  obtain ⟨x, hx, rfl⟩ := hw
  rw [hequiv]
  have hzfix := C.apartment.mem_pointwiseFixer.mp hz.2 (e x) ⟨x, hx, rfl⟩
  change (rationalExtend F (inertiaFixedField F) G g * z *
    (rationalExtend F (inertiaFixedField F) G g)⁻¹) •
      (rationalExtend F (inertiaFixedField F) G g • e x) = _
  simp only [mul_smul, inv_smul_smul, hzfix]

include hequiv hmodel in
/-- The extensions in opposite directions give a compatible isomorphism of actual models. -/
theorem exists_neutralConjugationIso (g : rationalPoints G) (Fc : BuildingFacet B) :
    Nonempty ((M.model Fc).neutral.Iso
      (M.model (B.facetTranslateEquiv g Fc)).neutral (G.innerIso g)) := by
  obtain ⟨φ⟩ := M.exists_neutralConjugationHom B C E e hequiv hmodel g Fc
  have hψ := M.exists_neutralConjugationHom B C E e hequiv hmodel
    g⁻¹ (B.facetTranslateEquiv g Fc)
  rw [B.facetTranslateEquiv_inv_apply, innerIso_inv_hom] at hψ
  obtain ⟨ψ⟩ := hψ
  exact ⟨IntegralModel.Iso.ofHoms φ ψ⟩

include hequiv hmodel in
/-- An actual integral section fixes the target facet after reflecting fixedness along e. -/
theorem facetTranslateEquiv_integralPointMap (hinj : Function.Injective e)
    (Fc : BuildingFacet B) (s : (M.model Fc).neutral.integralSections) :
    B.facetTranslateEquiv ((M.model Fc).neutral.integralPointMap s) Fc = Fc := by
  let g := (M.model Fc).neutral.integralPointMap s
  have hg := ((M.model Fc).neutral.mem_integralPoints_rationalExtend_iff_unramified g).mpr
    (show g ∈ (M.model Fc).neutral.integralPoints from ⟨s, rfl⟩)
  rw [hmodel] at hg
  have hfix (x : B.ReducedBuilding) (hx : x ∈ Fc.val) : g • x = x := by
    apply hinj
    rw [hequiv]
    exact C.apartment.mem_pointwiseFixer.mp hg.2 (e x) ⟨x, hx, rfl⟩
  apply Subtype.ext
  change (fun x => g • x) '' Fc.val = Fc.val
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change g • y ∈ Fc.val
    rwa [hfix y hy]
  · intro hx
    exact ⟨x, hx, hfix x hx⟩

/-- Generic rigidity compares the translated source morphism with target inner conjugation. -/
theorem neutralConjugationIso_comp_morphism
    (Fc Fd : BuildingFacet B) (hFD : FacetPrecedes B Fc Fd)
    (s : (M.model Fc).neutral.integralSections)
    (ht : FacetPrecedes B Fc
      (B.facetTranslateEquiv ((M.model Fc).neutral.integralPointMap s) Fd))
    (α : (M.model Fd).neutral.Iso
      (M.model (B.facetTranslateEquiv ((M.model Fc).neutral.integralPointMap s) Fd)).neutral
      (G.innerIso ((M.model Fc).neutral.integralPointMap s))) :
    α.iso.hom ≫ (M.morphism Fc _ ht).neutral.hom =
      (M.morphism Fc Fd hFD).neutral.hom ≫
        ((M.model Fc).neutral.innerHom s).hom := by
  let φ : (M.model Fd).neutral.Hom (M.model Fc).neutral
      (G.innerIso ((M.model Fc).neutral.integralPointMap s)).hom := by
    simpa only [Category.comp_id] using α.toHom.comp (M.morphism Fc _ ht).neutral
  let ψ : (M.model Fd).neutral.Hom (M.model Fc).neutral
      (G.innerIso ((M.model Fc).neutral.integralPointMap s)).hom := by
    simpa only [Category.id_comp] using
      (M.morphism Fc Fd hFD).neutral.comp ((M.model Fc).neutral.innerHom s)
  exact φ.hom_eq ψ

include hequiv hmodel in
/-- Translate the source facet to realize conjugation of its actual quotient image. -/
theorem exists_translated_incidentFacet_quotientImage
    (hinj : Function.Injective e)
    (Fc : BuildingFacet B) (Q : SpecialFibreQuotientData (M.model Fc))
    (Fd : IncidentFacets B Fc) (s : (M.model Fc).neutral.integralSections) :
    ∃ Ft : IncidentFacets B Fc,
      Ft.val = B.facetTranslateEquiv ((M.model Fc).neutral.integralPointMap s) Fd.val ∧
      M.incidentParabolicImage Fc Q Ft =
        SubgroupFunctor.range (SchematicImage.inclusion
          (((M.morphism Fc Fd.val Fd.property).neutralSpecialFibreMap ≫ Q.projection) ≫
            (Q.quotient.innerIso
              ((M.model Fc).neutral.reduction s ≫ Q.projection.hom.hom)).hom)) := by
  let g := (M.model Fc).neutral.integralPointMap s
  have ht : FacetPrecedes B Fc (B.facetTranslateEquiv g Fd.val) := by
    have h := B.facetPrecedes_translate g Fd.property
    rwa [M.facetTranslateEquiv_integralPointMap B C E e hequiv hmodel hinj Fc s] at h
  obtain ⟨α⟩ := M.exists_neutralConjugationIso B C E e hequiv hmodel g Fd.val
  have hsquare := M.neutralConjugationIso_comp_morphism B Fc Fd.val Fd.property s ht α
  let Rb := GroupScheme.baseChange (IntegralModel.residueBaseMap ↥𝒪[F])
  have hres :
      Rb.map α.iso.hom ≫ (M.morphism Fc _ ht).neutralSpecialFibreMap =
        (M.morphism Fc Fd.val Fd.property).neutralSpecialFibreMap ≫
          ((M.model Fc).neutral.specialFibre.innerIso
            ((M.model Fc).neutral.reduction s)).hom := by
    rw [← (M.model Fc).neutral.innerHom_specialFibreMap s]
    simpa only [Rb, g, Functor.map_comp, IntegralModel.Hom.specialFibreMap] using
      congrArg Rb.map hsquare
  have hquot :
      Rb.map α.iso.hom ≫
          ((M.morphism Fc _ ht).neutralSpecialFibreMap ≫ Q.projection) =
        ((M.morphism Fc Fd.val Fd.property).neutralSpecialFibreMap ≫ Q.projection) ≫
          (Q.quotient.innerIso
            ((M.model Fc).neutral.reduction s ≫ Q.projection.hom.hom)).hom := by
    rw [← Category.assoc, hres, Category.assoc, innerIso_hom_comp, Category.assoc]
  refine ⟨⟨B.facetTranslateEquiv g Fd.val, ht⟩, rfl, ?_⟩
  change SubgroupFunctor.range
      (SchematicImage.inclusion
        ((M.morphism Fc _ ht).neutralSpecialFibreMap ≫ Q.projection)) = _
  rw [← hquot]
  exact (SchematicImage.range_inclusion_iso_comp (Rb.mapIso α.iso) _).symm

end Langlands.BruhatTits.IntegralModels.FacetModelData

namespace Langlands.BruhatTits.IntegralModels

/-- Every residue-field parabolic at an apartment point is an actual incident facet image. -/
def UnramifiedResidueParabolicAttainmentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)
    (R : P.toValuationBuildingData.PolysimplicialRealization)
    (T : P.toValuationBuildingData.ApartmentSplitting),
    P.SatisfiesBuildingAxiom R →
    P.HasBoundedOpenStabilizers →
    P.SatisfiesAffineApartmentAxiom T →
    P.HasRootReflections →
    P.SatisfiesApartmentAxioms →
    P.HasCompatibleApartmentFacets →
    P.HasTitsSystem →
    ∀ (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
      (A : MaximalUnramified.SemilinearApartmentData C)
      (e : P.toValuationBuildingData.ReducedBuilding → C.ReducedBuilding)
      (a : P.toValuationBuildingData.Apartment →ᵃ[ℝ] C.Apartment),
      Function.Injective e →
      (∀ (g : rationalPoints G) (z : P.toValuationBuildingData.ReducedBuilding),
        e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z) →
      (∀ w : P.toValuationBuildingData.Apartment,
        e (P.toValuationBuildingData.apartmentMap w) = C.apartmentMap (a w)) →
      (∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
          (z : P.toValuationBuildingData.ReducedBuilding),
        A.action σ (e z) = e z) →
      (∀ y : C.ReducedBuilding,
        (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F, A.action σ y = y) →
          ∃ z : P.toValuationBuildingData.ReducedBuilding, e z = y) →
      (∀ z : P.toValuationBuildingData.ReducedBuilding,
        C.IsSpecialPoint (e z) → P.toValuationBuildingData.IsSpecialPoint z) →
      (∀ w : P.toValuationBuildingData.Apartment,
        a ⁻¹' AffineRootSystem.facet C.affineRoots (a w) =
          AffineRootSystem.facet P.toValuationBuildingData.affineRoots w) →
      (∀ s ∈ characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) P.S.toGrp),
        ∀ w : P.toValuationBuildingData.Apartment,
          rationalPoints.map
              ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map P.i) s •
            e (P.toValuationBuildingData.apartmentMap w) =
              e (P.toValuationBuildingData.apartmentMap w)) →
    ∀ (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
      (Mf : FacetModelData P.toValuationBuildingData ↥𝒪[F]),
      (∀ Fc : BuildingFacet P.toValuationBuildingData,
        (Mf.model Fc).neutral.IsSmooth ∧
          (Mf.model Fc).neutral.baseChangeUnramified.integralPoints =
            E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val)) →
      ∀ (x : P.toValuationBuildingData.Apartment)
        (Q : SpecialFibreQuotientData
          (Mf.model (P.toValuationBuildingData.buildingFacetAt
            (P.toValuationBuildingData.apartmentMap x)))),
        Q.IsReductiveQuotient →
        ∀ (H : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥𝒪[F]))))
          (j : H ⟶ Q.quotient), IsParabolicSubgroup j →
          ∃ Fd : IncidentFacets P.toValuationBuildingData
              (P.toValuationBuildingData.buildingFacetAt
                (P.toValuationBuildingData.apartmentMap x)),
            Mf.incidentParabolicImage _ Q Fd = SubgroupFunctor.range j

/-- Absorb inverse integral conjugation by translating the actual source facet. -/
theorem unramifiedResidueParabolicAttainment :
    UnramifiedResidueParabolicAttainmentStatement.{u} := by
  intro F _ _ _ _ G _ P R T hbuilding hopen haff hroot hapt hfacet htits C A e a hinj hequiv hap hfixed hsurj hspecial hfacets hkernel E Mf hmodel x Q hQ H j hj
  obtain ⟨s, Fd, hFd⟩ := unramifiedResidueConjugateAttainment F G P R T
    hbuilding hopen haff hroot hapt hfacet htits C A e a
    hinj hequiv hap hfixed hsurj hspecial hfacets hkernel E Mf hmodel x Q hQ H j hj
  obtain ⟨Ft, _, hFt⟩ := Mf.exists_translated_incidentFacet_quotientImage
    P.toValuationBuildingData C E e hequiv (fun Fc => (hmodel Fc).2) hinj
    (P.toValuationBuildingData.buildingFacetAt
      (P.toValuationBuildingData.apartmentMap x)) Q Fd s⁻¹
  refine ⟨Ft, hFt.trans ?_⟩
  have hs :
      (Mf.model (P.toValuationBuildingData.buildingFacetAt
        (P.toValuationBuildingData.apartmentMap x))).neutral.reduction s⁻¹ ≫
          Q.projection.hom.hom =
      ((Mf.model (P.toValuationBuildingData.buildingFacetAt
        (P.toValuationBuildingData.apartmentMap x))).neutral.reduction s ≫
          Q.projection.hom.hom)⁻¹ := by
    exact map_inv ((rationalPoints.map Q.projection).comp
      (Mf.model (P.toValuationBuildingData.buildingFacetAt
        (P.toValuationBuildingData.apartmentMap x))).neutral.reduction) s
  rw [hs, innerIso_inv_hom]
  exact hFd

end Langlands.BruhatTits.IntegralModels
