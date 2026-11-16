import Langlands.BruhatTits.IntegralModels.UnramifiedFacetConjugation
import Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientTransport

/-! # Actual residue parabolic attainment at every descended facet -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building Langlands.LocalGalois.Separable
open Langlands.BruhatTits.IntegralModels
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- Each actual facet is the translate of the facet of a distinguished apartment point. -/
theorem exists_facetTranslate_apartmentPoint
    (hD : B.SatisfiesApartmentAxioms) (Fc : BuildingFacet B) :
    ∃ (g : rationalPoints G) (x : B.Apartment),
      Fc = B.facetTranslateEquiv g (B.buildingFacetAt (B.apartmentMap x)) := by
  obtain ⟨g, Fa, ⟨x, rfl⟩, hFc⟩ := Fc.property
  have hx : B.buildingFacetAt (g • B.apartmentMap x) = Fc := by
    apply (B.buildingFacetAt_eq_iff_mem hD _ Fc).mpr
    rw [hFc]
    exact ⟨x, AffineRootSystem.mem_facet_self _ _, rfl⟩
  rw [B.buildingFacetAt_eq_translate hD] at hx
  exact ⟨g, x, hx.symm⟩

end Langlands.Geometry.Building.ValuationBuildingData

namespace Langlands.BruhatTits.IntegralModels.FacetModelData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G) (M : FacetModelData B ↥𝒪[F])

/-- Simultaneous source and target conjugation commutes with the supplied family morphisms. -/
theorem conjugationIso_morphism_square
    (g : rationalPoints G) (Fc : BuildingFacet B) (Fd : IncidentFacets B Fc)
    (α : (M.model Fd.val).neutral.Iso
      (M.model (B.facetTranslateEquiv g Fd.val)).neutral (G.innerIso g))
    (β : (M.model Fc).neutral.Iso
      (M.model (B.facetTranslateEquiv g Fc)).neutral (G.innerIso g)) :
    α.iso.hom ≫
        (M.morphism (B.facetTranslateEquiv g Fc) (B.facetTranslateEquiv g Fd.val)
          (B.facetPrecedes_translate g Fd.property)).neutral.hom =
      (M.morphism Fc Fd.val Fd.property).neutral.hom ≫ β.iso.hom := by
  let φ : (M.model Fd.val).neutral.Hom
      (M.model (B.facetTranslateEquiv g Fc)).neutral (G.innerIso g).hom := by
    simpa only [Category.comp_id] using α.toHom.comp
      (M.morphism _ _ (B.facetPrecedes_translate g Fd.property)).neutral
  let ψ : (M.model Fd.val).neutral.Hom
      (M.model (B.facetTranslateEquiv g Fc)).neutral (G.innerIso g).hom := by
    simpa only [Category.id_comp] using
      (M.morphism Fc Fd.val Fd.property).neutral.comp β.toHom
  exact φ.hom_eq ψ

/-- Transporting the target quotient makes simultaneous facet translation preserve its image. -/
theorem incidentParabolicImage_translate_transportQuotient
    (g : rationalPoints G) (Fc : BuildingFacet B) (Fd : IncidentFacets B Fc)
    (α : (M.model Fd.val).neutral.Iso
      (M.model (B.facetTranslateEquiv g Fd.val)).neutral (G.innerIso g))
    (β : (M.model Fc).neutral.Iso
      (M.model (B.facetTranslateEquiv g Fc)).neutral (G.innerIso g))
    (Q : SpecialFibreQuotientData (M.model (B.facetTranslateEquiv g Fc))) :
    M.incidentParabolicImage (B.facetTranslateEquiv g Fc) Q
        ⟨B.facetTranslateEquiv g Fd.val, B.facetPrecedes_translate g Fd.property⟩ =
      M.incidentParabolicImage Fc
        (Q.transportSpecialFibreIso
          (((GroupScheme.baseChange (IntegralModel.residueBaseMap ↥𝒪[F])).mapIso
            β.iso).symm)) Fd := by
  let Rb := GroupScheme.baseChange (IntegralModel.residueBaseMap ↥𝒪[F])
  have hsquare := M.conjugationIso_morphism_square B g Fc Fd α β
  have hres :
      Rb.map α.iso.hom ≫
          (M.morphism (B.facetTranslateEquiv g Fc) (B.facetTranslateEquiv g Fd.val)
            (B.facetPrecedes_translate g Fd.property)).neutralSpecialFibreMap =
        (M.morphism Fc Fd.val Fd.property).neutralSpecialFibreMap ≫ Rb.map β.iso.hom := by
    simpa only [Rb, Functor.map_comp, IntegralModel.Hom.specialFibreMap] using
      congrArg Rb.map hsquare
  change SubgroupFunctor.range (SchematicImage.inclusion
      ((M.morphism _ _ (B.facetPrecedes_translate g Fd.property)).neutralSpecialFibreMap ≫
        Q.projection)) =
    SubgroupFunctor.range (SchematicImage.inclusion
      ((M.morphism Fc Fd.val Fd.property).neutralSpecialFibreMap ≫
        (Rb.map β.iso.hom ≫ Q.projection)))
  rw [← Category.assoc, ← hres, Category.assoc]
  exact (SchematicImage.range_inclusion_iso_comp (Rb.mapIso α.iso) _).symm

end Langlands.BruhatTits.IntegralModels.FacetModelData

namespace Langlands.BruhatTits.IntegralModels

/-- Every residue-field parabolic at any supplied facet model is an actual incident image. -/
def UnramifiedFacetParabolicSurjectivityStatement : Prop :=
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
      ∀ (Fc : BuildingFacet P.toValuationBuildingData)
        (Q : SpecialFibreQuotientData (Mf.model Fc)),
        Q.IsReductiveQuotient →
        ∀ (H : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥𝒪[F]))))
          (j : H ⟶ Q.quotient), IsParabolicSubgroup j →
          ∃ Fd : IncidentFacets P.toValuationBuildingData Fc,
            Mf.incidentParabolicImage Fc Q Fd = SubgroupFunctor.range j

/-- Translate an apartment-point attainment together with the actual target quotient. -/
theorem unramifiedFacetParabolicSurjectivity :
    UnramifiedFacetParabolicSurjectivityStatement.{u} := by
  intro F _ _ _ _ G _ P R T hbuilding hopen haff hroot hapt hfacet htits C A e a hinj hequiv hap hfixed hsurj hspecial hfacets hkernel E Mf hmodel Fc Q hQ H j hj
  let B := P.toValuationBuildingData
  obtain ⟨g, x, rfl⟩ := B.exists_facetTranslate_apartmentPoint hapt Fc
  let Fc₀ := B.buildingFacetAt (B.apartmentMap x)
  obtain ⟨β⟩ := Mf.exists_neutralConjugationIso B C E e hequiv
    (fun Fc => (hmodel Fc).2) g Fc₀
  let Rb := GroupScheme.baseChange (IntegralModel.residueBaseMap ↥𝒪[F])
  let Q₀ := Q.transportSpecialFibreIso (Rb.mapIso β.iso).symm
  have hQ₀ : Q₀.IsReductiveQuotient :=
    Q.isReductiveQuotient_transportSpecialFibreIso _ hQ
  obtain ⟨Fd, hFd⟩ := unramifiedResidueParabolicAttainment F G P R T
    hbuilding hopen haff hroot hapt hfacet htits C A e a
    hinj hequiv hap hfixed hsurj hspecial hfacets hkernel E Mf hmodel x Q₀ hQ₀ H j hj
  obtain ⟨α⟩ := Mf.exists_neutralConjugationIso B C E e hequiv
    (fun Fc => (hmodel Fc).2) g Fd.val
  refine ⟨⟨B.facetTranslateEquiv g Fd.val, B.facetPrecedes_translate g Fd.property⟩, ?_⟩
  exact (Mf.incidentParabolicImage_translate_transportQuotient B g Fc₀ Fd α β Q).trans hFd

end Langlands.BruhatTits.IntegralModels
