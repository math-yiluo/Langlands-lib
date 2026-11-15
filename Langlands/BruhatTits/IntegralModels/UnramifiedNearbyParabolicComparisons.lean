import Langlands.GroupScheme.IntegralModel.UnramifiedImagePreimage
import Langlands.BruhatTits.IntegralModels.SpecialFibreImageRecovery
import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralRadicalGeneration
import Langlands.BruhatTits.IntegralModels.UnramifiedNearbyNeutralComparison
import Langlands.BruhatTits.IntegralModels.ReductiveQuotientExistence
import Langlands.Geometry.Building.UnramifiedRecoveredDepthZeroOpposite
import Langlands.Geometry.Building.UnramifiedVertexMaximalBoundedProof
import Langlands.GroupScheme.IntegralModel.MaximalBoundedConstruction
import Langlands.GroupScheme.IntegralModel.SmoothIntersectionConstruction
import Langlands.GroupScheme.IntegralModel.UnramifiedSmoothDescentProof
import Langlands.GroupScheme.IntegralModel.UnramifiedSmoothHomExtensionProof
import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof

/-! # Nearby parabolic comparisons of recovered fixed-point models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter
open scoped ValuativeRel CategoryTheory.MonObj Topology
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.GroupScheme.RealTorusSpace Langlands.LocalGalois.Separable
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels.RelativeComponentModelData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}

private instance nearbyParabolic_specialFibre_affine [IsLocalRing R]
    (D : RelativeComponentModelData R K G) :
    IsAffineHom D.neutral.specialFibre.X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

private instance nearbyParabolic_specialFibre_isAffine [IsLocalRing R]
    (D : RelativeComponentModelData R K G) :
    IsAffine D.neutral.specialFibre.X.left :=
  isAffine_of_isAffineHom D.neutral.specialFibre.X.hom

private instance nearbyParabolic_specialFibre_smooth [IsLocalRing R]
    (D : RelativeComponentModelData R K G) :
    Smooth D.neutral.specialFibre.X.hom := by
  have : Smooth D.neutral.group.X.hom := D.neutral_smooth
  change Smooth (CategoryTheory.Limits.pullback.snd D.neutral.group.X.hom
    (IntegralModel.residueBaseMap R))
  infer_instance

private instance nearbyParabolic_specialFibre_connected [IsLocalRing R]
    (D : RelativeComponentModelData R K G) :
    ConnectedSpace D.neutral.specialFibre.X.left :=
  D.neutral.hasConnectedSpecialFibre_of_hasConnectedFibres D.neutral_connectedFibres

variable [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
  {source target : RelativeComponentModelData R K G}

/-- Congruence containment gives the exact actual-image reduction preimage of
any generic-identity map between the two neutral models, without a full-model map. -/
theorem neutralHom_imageReductionPreimage_eq_range
    (ψ : source.neutral.Hom target.neutral (𝟙 G))
    (hker : target.neutral.congruenceSubgroup ≤ source.neutral.integralPoints) :
    ψ.imageReductionPreimage = (rationalPoints.map ψ.hom).range := by
  apply le_antisymm _ ψ.sectionRange_le_imageReductionPreimage
  intro x hx
  have : GeometricallyIntegral source.neutral.specialFibre.X.hom :=
    smoothConnectedAffineGeometry.1 _ _ inferInstance inferInstance inferInstance
  have : Surjective (SchematicImage.projection ψ.specialFibreMap).hom.hom.left :=
    HomImage.surjective_projection ψ.specialFibreMap
  obtain ⟨z, hz⟩ := (SchematicImage.mem_rationalImage _ _).mp hx
  obtain ⟨w, rfl⟩ := GroupScheme.rationalPoints_surjective
    (SchematicImage.projection ψ.specialFibreMap) z
  obtain ⟨s, rfl⟩ := source.neutral.reduction_surjective source.neutral_smooth w
  have hred : target.neutral.reduction (rationalPoints.map ψ.hom s) =
      target.neutral.reduction x := by
    rw [ψ.reduction_naturality, ← hz]
    change source.neutral.reduction s ≫ ψ.specialFibreMap.hom.hom =
      (source.neutral.reduction s ≫
        (SchematicImage.projection ψ.specialFibreMap).hom.hom) ≫
          (SchematicImage.inclusion ψ.specialFibreMap).hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, SchematicImage.projection_inclusion]
  have hc : x * (rationalPoints.map ψ.hom s)⁻¹ ∈ target.neutral.congruenceKernel := by
    rw [IntegralModel.mem_congruenceKernel, map_mul, map_inv, hred, mul_inv_cancel]
  obtain ⟨s', hs'⟩ := hker ⟨_, hc, rfl⟩
  have h₁ : rationalPoints.map ψ.hom s' = x * (rationalPoints.map ψ.hom s)⁻¹ := by
    apply target.neutral.integralPointMap_injective
    rw [ψ.integralPointMap_identity]
    exact hs'
  refine ⟨s' * s, ?_⟩
  rw [map_mul, h₁, inv_mul_cancel_right]

end Langlands.BruhatTits.IntegralModels.RelativeComponentModelData

namespace Langlands.BruhatTits.IntegralModels

local instance nearbyParabolic_henselian {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    HenselianLocalRing (fixedFieldIntegers F) :=
  fixedFieldIntegersIsHenselian F

local instance nearbyParabolic_algClosed {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).1

section FacetClosure

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G)
    (M M' : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    {x y : C.Apartment}

/-- For the actual full fixer models of two points `x` and `y`, where `x`
lies in the closed facet of `y`, every generic-identity map from the neutral
model at `y` to the neutral model at `x` has parabolic actual special-fibre
image and exact actual-image reduction preimage. -/
theorem unramifiedNeutralFacetClosure_isParabolic_and_preimage
    (hM : M.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' {x}))
    (hM' : M'.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' {y}))
    (hxy : x ∈ AffineRootSystem.facetClosure C.affineRoots y)
    (ψ : M'.neutral.Hom M.neutral (𝟙 G)) :
    IsParabolicSubgroup (SchematicImage.inclusion ψ.specialFibreMap) ∧
      ψ.imageReductionPreimage = (rationalPoints.map ψ.hom).range := by
  have hCa : AffineRootSystem.IsFacet C.affineRoots
      (AffineRootSystem.facet C.affineRoots y) :=
    AffineRootSystem.isFacet_facet _ y
  have hFaCa : AffineRootSystem.IsFaceOf C.affineRoots
      (AffineRootSystem.facet C.affineRoots x) (AffineRootSystem.facet C.affineRoots y) :=
    ⟨AffineRootSystem.isFacet_facet _ x, y, rfl,
      AffineRootSystem.facet_subset_facetClosure_iff.mpr hxy⟩
  have hsub : ({x} : Set C.Apartment) ⊆ AffineRootSystem.facet C.affineRoots x :=
    Set.singleton_subset_iff.mpr (AffineRootSystem.mem_facet_self _ x)
  have hsub' : ({y} : Set C.Apartment) ⊆ AffineRootSystem.facet C.affineRoots y :=
    Set.singleton_subset_iff.mpr (AffineRootSystem.mem_facet_self _ y)
  obtain ⟨Q, hQ⟩ := SpecialFibreQuotientData.exists_isReductiveQuotient M
  refine ⟨?_, ?_⟩
  · exact unramifiedNeutralIncidentImage_isParabolic_of_facet C M {x} hM
      (Set.singleton_nonempty x) hsub Q hQ M' {y} hM' hCa hFaCa hsub' ψ
      (Set.singleton_nonempty y)
  · exact RelativeComponentModelData.neutralHom_imageReductionPreimage_eq_range ψ
      (unramifiedNeutralIncidentCongruence_le_neutral_of_facet C M {x} hM
        (Set.singleton_nonempty x) hsub M' {y} hM' hCa hFaCa hsub')

end FacetClosure

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {iT : T.toGrp ⟶ G}
  [Mono ((GroupScheme.baseChange
    (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  {D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F))}
  (hG : IsConnectedReductive G)
  (hiT : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)

private instance nearbyParabolicExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

include hG hiT hDC

namespace RecoveredApartmentFixerModels

/-- If `x` lies in the closed facet of `y`, every generic-identity map from the
actual upper neutral model at `y` to that at `x` has parabolic actual image and
exact actual-image reduction preimage. -/
theorem upper_neutralHom_parabolic_and_preimage
    {x y : D.Apartment}
    (X : RecoveredApartmentFixerModels D {x}) (Y : RecoveredApartmentFixerModels D {y})
    (hxy : x ∈ AffineRootSystem.facetClosure D.affineRoots y)
    (ψ : Y.upper.neutral.Hom X.upper.neutral (𝟙 _)) :
    IsParabolicSubgroup (SchematicImage.inclusion ψ.specialFibreMap) ∧
      ψ.imageReductionPreimage = (rationalPoints.map ψ.hom).range := by
  let B := MaximalUnramified.buildingDataOfApartment hG hiT D C hDC
  have hxy' : x ∈ AffineRootSystem.facetClosure B.affineRoots y := by
    dsimp only [IntegerValuationBuildingData.affineRoots, B,
      MaximalUnramified.buildingDataOfApartment]
    exact hxy
  exact unramifiedNeutralFacetClosure_isParabolic_and_preimage B X.upper Y.upper
    X.full_integralPoints Y.full_integralPoints hxy' ψ

end RecoveredApartmentFixerModels

namespace RecoveredFixedNearbyModels

variable {f : S ⟶ T} {hS : IsSplitTorus S.toGrp} {x : D.Apartment}
  (M : RecoveredFixedNearbyModels D f hS x)

/-- Every recovered nearby-model package at a coefficient-fixed point has
parabolic comparison images and exact reduction preimages near zero. -/
theorem hasParabolicComparisonsNear
    (hx : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val) :
    M.HasParabolicComparisonsNear := by
  intro v
  let N : ∀ t : ℝ, RecoveredApartmentFixerModels D
      {D.descentTranslate f hS x (t • v)} := fun t =>
    recoveredFixedPointModelsOfVertexInputs D
      MaximalUnramified.vertexOneStabilizerMaximalBounded maximalBoundedIntegralModel
      IntegralModel.smoothIntersection IntegralModel.unramifiedSmoothModelDescent
      hG hiT C hDC _ (D.galois_fixed_descentTranslate f hS x hx (t • v))
  filter_upwards [M.eventually_source_neutral_integralPoints_eq_endpoint hG hiT C hDC v N,
    D.eventually_mem_facetClosure_descentTranslate f hS hG hiT C hDC x v] with t ht hxy
  have hle : (N t).upper.neutral.integralPoints ≤
      M.target.upper.neutral.integralPoints := by
    rw [← ht.1]
    exact ((M.source (t • v)).recovery.nonempty_neutralHom_iff M.target.recovery
      IntegralModel.unramifiedSmoothHomExtension).mp ⟨(M.comparison (t • v)).neutral⟩
  obtain ⟨ψ⟩ := IntegralModel.fixedField_hasSmoothHomExtension
    IntegralModel.smoothHomExtension F _ _ (𝟙 _) (N t).upper.neutral
    M.target.upper.neutral (N t).upper.neutral_smooth (by
      intro g hg
      simpa only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id] using hle hg)
  obtain ⟨hpar, hpre⟩ := RecoveredApartmentFixerModels.upper_neutralHom_parabolic_and_preimage
    hG hiT C hDC M.target (N t) hxy ψ
  have hsource : (M.source (t • v)).lower.neutral.baseChangeUnramified.integralPoints =
      (N t).upper.neutral.integralPoints :=
    (M.source (t • v)).recovery.neutral_integralPoints_eq.trans ht.1
  exact ⟨(M.comparison (t • v)).hasParabolicSpecialFibreImage_of_unramifiedModels
      _ _ (N t).upper.neutral_smooth M.target.upper.neutral_smooth hsource
      M.target.recovery.neutral_integralPoints_eq ψ hpar,
    (M.comparison (t • v)).hasParabolicReductionPreimage_of_unramifiedModels
      _ _ (N t).upper.neutral_smooth M.target.upper.neutral_smooth hsource
      M.target.recovery.neutral_integralPoints_eq ψ hpre⟩

end RecoveredFixedNearbyModels

end Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

open Langlands.BruhatTits.IntegralModels

/-- The recovered singleton models with nearby parabolic root comparisons are
available at every coefficient-fixed apartment point. -/
theorem unramifiedFixedRecoveredParabolicModels :
    UnramifiedFixedRecoveredParabolicModelsStatement.{u} := by
  intro F _ _ _ _ G hG S iS hiS T iT f hf
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  have := mono_of_isMaximalSplitTorus hiS
  intro hiT
  have : Mono ((GroupScheme.baseChange
    (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
      mono_of_isMaximalSplitTorus hiT
  intro hE D C hDC z hz
  have hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G) :=
    hG.baseChange_of_algebraicExtension
  let M := recoveredFixedNearbyModelsOfVertexInputs D f hiS.isSplitSubtorus.1
    MaximalUnramified.vertexOneStabilizerMaximalBounded maximalBoundedIntegralModel
    IntegralModel.smoothIntersection IntegralModel.unramifiedSmoothModelDescent
    IntegralModel.unramifiedSmoothHomExtension hG hiT C hDC z hz
  exact ⟨M.target.lower, M.target.upper, M.target.recovery, M.target.full_integralPoints,
    M.parabolicRootComparisonsNear hGK hiT hf hE (M.hasParabolicComparisonsNear hG hiT C hDC hz)⟩

end Langlands.Geometry.Building
