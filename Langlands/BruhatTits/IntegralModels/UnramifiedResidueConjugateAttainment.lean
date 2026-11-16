import Langlands.BruhatTits.IntegralModels.UnramifiedResidueFixedTorusAttainment
import Langlands.Geometry.Building.UnramifiedDescendedApartmentTorusProof
import Langlands.Geometry.Building.CommonApartmentConstruction
import Langlands.GroupScheme.IntegralModel.QuotientLifting
import Langlands.GroupScheme.Dynamic.PresentationComparison

/-! # Integral conjugates of actual downstairs facet images -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData

/-- Over a Henselian base with perfect residue field, the actual quotient
reduction map of a smooth neutral model is surjective. -/
theorem quotientReduction_surjective
    {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [HenselianLocalRing R]
    [PerfectField (IsLocalRing.ResidueField R)]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {D : RelativeComponentModelData R K G}
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient) :
    Function.Surjective ((rationalPoints.map Q.projection).comp D.neutral.reduction) := by
  let : Smooth Q.radical.X.hom := hQ.1.smooth
  let : ConnectedSpace Q.radical.X.left := hQ.1.connectedSpace
  let : IsAffineHom D.neutral.specialFibre.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
      (IntegralModel.residueBaseMap R))
    infer_instance
  let : IsAffineHom Q.radical.X.hom :=
    HomogeneousQuotient.affine_subgroup_of_closed
      D.neutral.specialFibre Q.radical Q.radicalInclusion hQ.1.isClosedSubgroup
  exact D.neutral.quotientReduction_surjective D.neutral_smooth
    Q.radicalInclusion hQ.1.isClosedSubgroup
    (perfectFieldUnipotentSplit _ Q.radical inferInstance hQ.1.isUnipotent)
    Q.projection hQ.2.1

end Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData

namespace Langlands.BruhatTits.IntegralModels.FacetModelData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)
  (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
  (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
  (e : B.ReducedBuilding → C.ReducedBuilding)
  (a : B.Apartment →ᵃ[ℝ] C.Apartment)
  (hD : B.SatisfiesApartmentAxioms)
  (hcommon : ∀ z : B.ReducedBuilding, B.HasCommonApartmentWith z)
  (hequiv : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
    e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
  (hap : ∀ x : B.Apartment, e (B.apartmentMap x) = C.apartmentMap (a x))
  (hfac : ∀ x : B.Apartment,
    a ⁻¹' AffineRootSystem.facet C.affineRoots (a x) =
      AffineRootSystem.facet B.affineRoots x)
  (M : FacetModelData B ↥𝒪[F])
  (hmodel : ∀ Fc : BuildingFacet B,
    (M.model Fc).neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val))

private instance residueConjugate_affine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

local instance : HenselianLocalRing ↥𝒪[F] := henselianLocalRing_integer

include hD hcommon hequiv hap hfac hmodel in
/-- Any residue parabolic is the inverse integral conjugate of an actual
supplied facet-model quotient image. -/
theorem exists_integralConjugate_incidentFacet_quotientImage_eq_parabolic
    (f : baseChanged F (inertiaFixedField F) B.S.toGrp ⟶ C.S.toGrp)
    (hf : f ≫ C.i =
      (GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map B.i)
    (x : B.Apartment)
    (Q : SpecialFibreQuotientData (M.model (B.buildingFacetAt (B.apartmentMap x))))
    (hQ : Q.IsReductiveQuotient)
    (T : IntegralTorusData (M.model (B.buildingFacetAt (B.apartmentMap x))) B.S B.i)
    (hT : T.SatisfiesTorusClause)
    (P : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥𝒪[F]))))
    (j : P ⟶ Q.quotient) (hj : IsParabolicSubgroup j) :
    ∃ s : (M.model (B.buildingFacetAt (B.apartmentMap x))).neutral.integralSections,
      ∃ Fd : IncidentFacets B (B.buildingFacetAt (B.apartmentMap x)),
        SubgroupFunctor.range (SchematicImage.inclusion
          (((M.morphism _ Fd.val Fd.property).neutralSpecialFibreMap ≫ Q.projection) ≫
            (Q.quotient.innerIso
              ((M.model (B.buildingFacetAt (B.apartmentMap x))).neutral.reduction s ≫
                Q.projection.hom.hom)).inv)) = SubgroupFunctor.range j := by
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  let : ConnectedSpace Q.quotient.X.left := hQ.2.2.connectedSpace
  obtain ⟨χ, hχ⟩ := (parabolicDynamic _ Q.quotient hQ.2.2 P j hj.isClosedSubgroup).mp hj
  obtain ⟨g, ν, hν⟩ := exists_innerIso_comp_eq_cocharacter
    smoothMaximalSplitTorusConjugacy
    (T.isMaximalSplitTorus_quotient Q hQ hT.2) χ
  obtain ⟨s, hs⟩ := Q.quotientReduction_surjective hQ g
  change (M.model (B.buildingFacetAt (B.apartmentMap x))).neutral.reduction s ≫
    Q.projection.hom.hom = g at hs
  let c := (T.cocharacterSpecialization hT.1.1).symm ν
  obtain ⟨ε, hε, Fd, hFd, himage⟩ :=
    M.exists_incidentFacet_quotientImage_eq_residueCocharacter
      B C E e a hD hcommon hequiv hap hfac hmodel f hf x Q hQ T hT.1.1 c
  have heq : SubgroupFunctor.range (j ≫ (Q.quotient.innerIso g).hom) =
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫
        (T.specialFibreInclusion ≫ Q.projection)) := by
    rw [← hν]
    exact (Dynamic.range_eq_parabolic_comp_iso_iff j χ (Q.quotient.innerIso g)).mpr hχ
  have himage' : SubgroupFunctor.range
      ((M.morphism _ Fd.val Fd.property).reductiveImageInclusion Q) =
        SubgroupFunctor.range (j ≫ (Q.quotient.innerIso g).hom) := by
    rw [heq]
    simpa only [c, AddEquiv.apply_symm_apply, Category.assoc] using himage
  refine ⟨s, Fd, ?_⟩
  rw [hs]
  calc
    _ = (SubgroupFunctor.range
        ((M.morphism _ Fd.val Fd.property).reductiveImageInclusion Q)).comap
          (Q.quotient.innerIso g).hom :=
      SchematicImage.range_inclusion_comp_iso
        ((M.morphism _ Fd.val Fd.property).neutralSpecialFibreMap ≫ Q.projection)
        (Q.quotient.innerIso g).symm
    _ = _ := by
      rw [himage', SubgroupFunctor.range_comp_iso j (Q.quotient.innerIso g),
        ← SubgroupFunctor.comap_comp, Iso.hom_inv_id, SubgroupFunctor.comap_id]

end Langlands.BruhatTits.IntegralModels.FacetModelData

namespace Langlands.BruhatTits.IntegralModels

/-- Under the complete descended-building hypotheses, every parabolic of the
actual quotient at an apartment point is an inverse integral conjugate of
an incident facet-model image. -/
def UnramifiedResidueConjugateAttainmentStatement : Prop :=
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
          ∃ s : (Mf.model (P.toValuationBuildingData.buildingFacetAt
              (P.toValuationBuildingData.apartmentMap x))).neutral.integralSections,
            ∃ Fd : IncidentFacets P.toValuationBuildingData
                (P.toValuationBuildingData.buildingFacetAt
                  (P.toValuationBuildingData.apartmentMap x)),
              SubgroupFunctor.range (SchematicImage.inclusion
                (((Mf.morphism _ Fd.val Fd.property).neutralSpecialFibreMap ≫
                    Q.projection) ≫
                  (Q.quotient.innerIso
                    ((Mf.model (P.toValuationBuildingData.buildingFacetAt
                      (P.toValuationBuildingData.apartmentMap x))).neutral.reduction s ≫
                        Q.projection.hom.hom)).inv)) = SubgroupFunctor.range j

/-- The torus factorization and actual integral torus are constructed from
the host hypotheses, rather than supplied as additional premises. -/
theorem unramifiedResidueConjugateAttainment :
    UnramifiedResidueConjugateAttainmentStatement.{u} := by
  intro F _ _ _ _ G _ P R T hbuilding hopen haff hroot hapt hfacet htits C A e a hinj hequiv hap hfixed hsurj hspecial hfacets hkernel E Mf hmodel x Q hQ H j hj
  obtain ⟨f, hf⟩ := unramifiedDescendedApartmentTorus F G P R T
    hbuilding hopen haff hroot hapt hfacet htits C A e a
    hinj hequiv hap hfixed hsurj hspecial hfacets hkernel
  have hcommon := R.hasCommonApartmentWith_of_isBuilding hbuilding.isBuilding
  have hmodels := fun Fc => (hmodel Fc).2
  obtain ⟨S, hS⟩ := Mf.exists_integralTorus_at_apartmentPoint
    P.toValuationBuildingData C E e a hapt hcommon hequiv hap hfacets hmodels hkernel x
  exact Mf.exists_integralConjugate_incidentFacet_quotientImage_eq_parabolic
    P.toValuationBuildingData C E e a hapt hcommon hequiv hap hfacets hmodels
    f hf x Q hQ S hS H j hj

end Langlands.BruhatTits.IntegralModels
