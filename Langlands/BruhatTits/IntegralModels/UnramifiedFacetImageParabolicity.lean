import Langlands.BruhatTits.IntegralModels.UnramifiedFacetApartmentReduction
import Langlands.BruhatTits.IntegralModels.UnramifiedIncidentParabolicImage
import Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsRadicalRootGenerationStatement
import Langlands.BruhatTits.IntegralModels.UnramifiedComponentModelComparison
import Langlands.GroupScheme.IntegralModel.UnramifiedSpecialFibreImage
import Langlands.GroupScheme.IntegralModel.ConnectedFibreDescent
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof

/-! # Parabolicity of descended facet images from upstairs radical generation -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

namespace Langlands.GroupScheme.IntegralModel

section ConnectedBaseChange

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (M : IntegralModel R K G)
    (A L : Type u) [CommRing A] [IsDomain A] [Field L]
    [Algebra R A] [Algebra A L] [IsFractionRing A L]
    [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
    [IsLocalRing A] [IsLocalHom (algebraMap R A)]

/-- Connectedness of an actual model special fibre persists under any local
coefficient extension with the indicated fraction-field square. -/
theorem hasConnectedSpecialFibre_baseChange
    (hM : M.HasConnectedSpecialFibre) : (M.baseChange A L).HasConnectedSpecialFibre := by
  let : ConnectedSpace M.specialFibre.X.left := hM
  let : LocallyOfFiniteType M.specialFibre.X.hom := by
    change LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd M.group.X.hom (residueBaseMap R))
    infer_instance
  let : IsAffineHom M.specialFibre.X.hom := by
    change IsAffineHom
      (CategoryTheory.Limits.pullback.snd M.group.X.hom (residueBaseMap R))
    infer_instance
  have hc : ConnectedSpace ((GroupScheme.baseChange
      (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))).obj
        M.specialFibre).X.left :=
    M.specialFibre.connectedSpace_baseChange_of_connected _
  let q := (Over.forget _).mapIso
    ((Grp.forget _).mapIso (M.specialFibreBaseChangeIso A L))
  exact q.hom.homeomorph.connectedSpace_iff.mp hc

end ConnectedBaseChange
end Langlands.GroupScheme.IntegralModel

namespace Langlands.BruhatTits.IntegralModels

private instance facetImageParabolicityAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local instance facetImageParabolicityIntegerAlgebra :
    Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance facetImageParabolicityIntegerTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance facetImageParabolicityIntegerLocal :
    IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  Valuation.HasExtension.instIsLocalHomValuationInteger
    (vR := ValuativeRel.valuation F) (vS := fixedFieldValuation F)

namespace RelativeComponentModelData

variable (D : RelativeComponentModelData ↥𝒪[F] F G)

omit [IsAffineHom G.X.hom] in
/-- The actual extended neutral model has a connected full special fibre. -/
theorem unramifiedNeutral_hasConnectedSpecialFibre :
    D.neutral.baseChangeUnramified.HasConnectedSpecialFibre := by
  exact D.neutral.hasConnectedSpecialFibre_baseChange
    (fixedFieldIntegers F) (inertiaFixedField F)
    (D.neutral.hasConnectedSpecialFibre_of_hasConnectedFibres D.neutral_connectedFibres)

private instance facetImageParabolicityNeutralSpecialFibreAffine :
    IsAffineHom D.neutral.baseChangeUnramified.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd
    D.neutral.baseChangeUnramified.group.X.hom
    (IntegralModel.residueBaseMap (fixedFieldIntegers F)))
  exact MorphismProperty.pullback_snd _ _ D.neutral.baseChangeUnramified.affine

private instance facetImageParabolicityNeutralSpecialFibreSmooth :
    Smooth D.neutral.baseChangeUnramified.specialFibre.X.hom := by
  let : Smooth D.neutral.baseChangeUnramified.group.X.hom :=
    D.neutral.isSmooth_baseChange (fixedFieldIntegers F) (inertiaFixedField F)
      D.neutral_smooth
  change Smooth (CategoryTheory.Limits.pullback.snd
    D.neutral.baseChangeUnramified.group.X.hom
    (IntegralModel.residueBaseMap (fixedFieldIntegers F)))
  infer_instance

/-- A chosen represented unipotent radical of the actual extended neutral
special fibre, together with its actual inclusion and radical proof. -/
def unramifiedNeutralRadicalData :
    Σ U : GroupScheme
      (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F)))),
      {i : U ⟶ D.neutral.baseChangeUnramified.specialFibre // IsUnipotentRadical i} :=
  Classical.choice <| by
    let : ConnectedSpace D.neutral.baseChangeUnramified.specialFibre.X.left :=
      D.unramifiedNeutral_hasConnectedSpecialFibre
    obtain ⟨U, i, hi⟩ := unipotentRadicalExistence
      (IsLocalRing.ResidueField (fixedFieldIntegers F))
      D.neutral.baseChangeUnramified.specialFibre
    exact ⟨⟨U, i, hi⟩⟩

end RelativeComponentModelData

/-- Full upstairs radical generation gives parabolicity for any two smooth
upstairs models characterized by incident downstairs facet images, when the
target special fibre is connected. -/
theorem unramifiedModelsImage_isParabolic_of_upstairs_rootGeneration
    (hgen : UnramifiedUpstairsRadicalRootGenerationStatement.{u})
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
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (Fc Fc' : BuildingFacet B) (hFC : FacetPrecedes B Fc Fc')
    (N N' : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    [Smooth N.group.X.hom] [Smooth N'.group.X.hom]
    [ConnectedSpace N.specialFibre.X.left]
    (hN : N.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val))
    (hN' : N'.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc'.val))
    (ψ : N'.Hom N (𝟙 (baseChanged F (inertiaFixedField F) G))) :
    IsParabolicSubgroup (SchematicImage.inclusion ψ.specialFibreMap) := by
  obtain ⟨g, Ω, Ω', Fa, Ca, hΩ, hΩ', hFa, hCa, hFaCa, hsub, hsub',
      _, _, hpts, hpts'⟩ :=
    exists_incident_apartment_models B C e a hequiv hap hfac E Fc Fc' hFC
      N N' hN hN' ψ
  let t := (baseChanged F (inertiaFixedField F) G).innerIso
    (rationalExtend F (inertiaFixedField F) G g)⁻¹
  let Nt := N.transport t
  let N't := N'.transport t
  let ψt := ψ.transportId t
  let : Smooth Nt.group.X.hom := inferInstanceAs (Smooth N.group.X.hom)
  let : Smooth N't.group.X.hom := inferInstanceAs (Smooth N'.group.X.hom)
  let : ConnectedSpace Nt.specialFibre.X.left :=
    inferInstanceAs (ConnectedSpace N.specialFibre.X.left)
  let : IsAffineHom Nt.specialFibre.X.hom :=
    MorphismProperty.pullback_snd _ _ Nt.affine
  let : Smooth Nt.specialFibre.X.hom :=
    MorphismProperty.pullback_snd _ _ (inferInstanceAs (Smooth Nt.group.X.hom))
  obtain ⟨U, r, hr⟩ := unipotentRadicalExistence
    (IsLocalRing.ResidueField (fixedFieldIntegers F)) Nt.specialFibre
  obtain ⟨H, _, hH, hgenerates⟩ := hgen F _ C E
  have hΩfacet : ∃ x : C.Apartment,
      Ω ⊆ AffineRootSystem.facet C.affineRoots x := by
    obtain ⟨x, hx⟩ := hFa
    exact ⟨x, hx ▸ hsub⟩
  have hroot := hgenerates Ω hΩ hΩfacet Nt
    (inferInstanceAs (Smooth Nt.group.X.hom)) hpts U r hr
  exact unramifiedIncidentImage_isParabolic_of_rootGeneration
    C E Nt N't Ω Ω' hpts hpts' ψt hCa hFaCa hΩ hΩ' hsub hsub'
    r hr H hH hroot.le

/-- Full upstairs radical generation implies parabolicity of the actual
neutral special-fibre image for characterized descended incident facets. -/
theorem unramifiedFacetImage_isParabolic_of_upstairs_rootGeneration
    (hgen : UnramifiedUpstairsRadicalRootGenerationStatement.{u})
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
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (Fc Fc' : BuildingFacet B) (hFC : FacetPrecedes B Fc Fc')
    (D D' : RelativeComponentModelData ↥𝒪[F] F G)
    (hN : D.neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val))
    (hN' : D'.neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc'.val))
    (φ : RelativeComponentModelHom D' D) :
    φ.HasParabolicSpecialFibreImage := by
  let : Smooth D.neutral.baseChangeUnramified.group.X.hom :=
    D.neutral.isSmooth_baseChange (fixedFieldIntegers F) (inertiaFixedField F)
      D.neutral_smooth
  let : Smooth D'.neutral.baseChangeUnramified.group.X.hom :=
    D'.neutral.isSmooth_baseChange (fixedFieldIntegers F) (inertiaFixedField F)
      D'.neutral_smooth
  let : ConnectedSpace D.neutral.baseChangeUnramified.specialFibre.X.left :=
    D.unramifiedNeutral_hasConnectedSpecialFibre
  have hpar := unramifiedModelsImage_isParabolic_of_upstairs_rootGeneration
    hgen B C e a hequiv hap hfac E Fc Fc' hFC
    D.neutral.baseChangeUnramified D'.neutral.baseChangeUnramified hN hN'
    (φ.neutral.baseChangeIdentity (fixedFieldIntegers F) (inertiaFixedField F))
  exact φ.neutral.isParabolic_specialFibreImage_of_unramified hpar

end Langlands.BruhatTits.IntegralModels
