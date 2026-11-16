import Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicOrderStatement
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetSurjectivity
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetImageParabolicity
import Langlands.BruhatTits.IntegralModels.UnramifiedIncidentParabolicEmbedding
import Langlands.BruhatTits.IntegralModels.FacetParabolicIncidence

/-! # The full descended facet order bijection from upstairs radical generation -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  (M N : IntegralModel R K G) (f : G ≅ H)

/-- Generic transport carries the actual congruence subgroup to its pointwise image. -/
theorem transport_congruenceSubgroup :
    (M.transport f).congruenceSubgroup =
      M.congruenceSubgroup.map (rationalPoints.map f.hom) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨M.integralPointMap x, ⟨x, hx, rfl⟩,
      (M.transport_integralPointMap f x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, M.transport_integralPointMap f x⟩

/-- Containment of the target congruence subgroup in source integral points
is preserved and reflected by simultaneous generic transport. -/
theorem congruenceSubgroup_le_integralPoints_transport_iff :
    (M.transport f).congruenceSubgroup ≤ (N.transport f).integralPoints ↔
      M.congruenceSubgroup ≤ N.integralPoints := by
  rw [M.transport_congruenceSubgroup f, N.transport_integralPoints f,
    Subgroup.map_le_map_iff_of_injective (rationalPoints_map_injective_of_iso f)]

end Langlands.GroupScheme.IntegralModel

namespace Langlands.BruhatTits.IntegralModels

private instance orderReduction_affine {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- The full radical preimage bound also contains the target congruence kernel,
so incident characterized upstairs models satisfy the required containment. -/
theorem unramifiedModels_congruenceSubgroup_le_of_upstairs_rootGeneration
    (hgen : UnramifiedUpstairsRadicalRootGenerationStatement.{u})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
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
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (Fc Fd : BuildingFacet B) (hFC : FacetPrecedes B Fc Fd)
    (N N' : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    [Smooth N.group.X.hom] [ConnectedSpace N.specialFibre.X.left]
    (hN : N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val))
    (hN' : N'.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (e '' Fd.val))
    (ψ : N'.Hom N (𝟙 (baseChanged F (inertiaFixedField F) G))) :
    N.congruenceSubgroup ≤ N'.integralPoints := by
  obtain ⟨g, Ω, Ω', Fa, Ca, hΩ, _, hFa, hCa, hFaCa, hsub, hsub',
      _, _, hpts, hpts'⟩ :=
    exists_incident_apartment_models B C e a hequiv hap hfac E Fc Fd hFC
      N N' hN hN' ψ
  let t := (baseChanged F (inertiaFixedField F) G).innerIso
    (rationalExtend F (inertiaFixedField F) G g)⁻¹
  let Nt := N.transport t
  let N't := N'.transport t
  let : Smooth Nt.group.X.hom := inferInstanceAs (Smooth N.group.X.hom)
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
  have hpre := unramifiedIncidentReductionPreimage_le_integralPoints
    C E Ω Ω' hCa hFaCa hΩ hsub hsub' H hH Nt N't hpts' r hroot.le
  apply (N.congruenceSubgroup_le_integralPoints_transport_iff N' t).mp
  apply le_trans _ hpre
  apply Subgroup.map_mono
  intro s hs
  change Nt.reduction s ∈ (rationalPoints.map r).range
  change Nt.reduction s = 1 at hs
  rw [hs]
  exact Subgroup.one_mem _

section IncidentImageEmbedding

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local instance orderReductionIntegerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance orderReductionIntegerTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance orderReductionIntegerLocal :
    IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  Valuation.HasExtension.instIsLocalHomValuationInteger
    (vR := ValuativeRel.valuation F) (vS := fixedFieldValuation F)

/-- Radical generation supplies the precise upstairs hypotheses for the
actual descended incident-image embedding. -/
theorem unramifiedIncidentImageEmbedding_of_upstairs_rootGeneration
    (hgen : UnramifiedUpstairsRadicalRootGenerationStatement.{u})
    (B : ValuationBuildingData G)
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (e : B.ReducedBuilding → C.ReducedBuilding)
    (a : B.Apartment →ᵃ[ℝ] C.Apartment)
    (hapt : B.SatisfiesApartmentAxioms)
    (hcommon : ∀ x : B.ReducedBuilding, B.HasCommonApartmentWith x)
    (hequiv : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
      e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
    (hap : ∀ x : B.Apartment, e (B.apartmentMap x) = C.apartmentMap (a x))
    (hfacets : ∀ x : B.Apartment,
      a ⁻¹' AffineRootSystem.facet C.affineRoots (a x) =
        AffineRootSystem.facet B.affineRoots x)
    (Mf : FacetModelData B ↥𝒪[F])
    (hmodel : ∀ Fd : BuildingFacet B,
      (Mf.model Fd).neutral.baseChangeUnramified.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer (e '' Fd.val))
    (Fc : BuildingFacet B) (Q : SpecialFibreQuotientData (Mf.model Fc))
    (hQ : Q.IsReductiveQuotient) :
    Set.MapsTo (Mf.incidentParabolicImage Fc Q) Set.univ {J | IsParabolicFunctor J} ∧
      Function.Injective (Mf.incidentParabolicImage Fc Q) := by
  have hpar (Fd : IncidentFacets B Fc) :
      ((Mf.morphism Fc Fd.val Fd.property).baseChange
        (fixedFieldIntegers F) (inertiaFixedField F)).HasParabolicSpecialFibreImage := by
    let : Smooth (Mf.model Fc).neutral.baseChangeUnramified.group.X.hom :=
      (Mf.model Fc).neutral.isSmooth_baseChange (fixedFieldIntegers F)
        (inertiaFixedField F) (Mf.model Fc).neutral_smooth
    let : Smooth (Mf.model Fd.val).neutral.baseChangeUnramified.group.X.hom :=
      (Mf.model Fd.val).neutral.isSmooth_baseChange (fixedFieldIntegers F)
        (inertiaFixedField F) (Mf.model Fd.val).neutral_smooth
    let : ConnectedSpace (Mf.model Fc).neutral.baseChangeUnramified.specialFibre.X.left :=
      (Mf.model Fc).unramifiedNeutral_hasConnectedSpecialFibre
    exact unramifiedModelsImage_isParabolic_of_upstairs_rootGeneration hgen
      B C e a hequiv hap hfacets E Fc Fd.val Fd.property
      (Mf.model Fc).neutral.baseChangeUnramified
      (Mf.model Fd.val).neutral.baseChangeUnramified
      (hmodel Fc) (hmodel Fd.val)
      ((Mf.morphism Fc Fd.val Fd.property).baseChange
        (fixedFieldIntegers F) (inertiaFixedField F)).neutral
  have hker (Fd : IncidentFacets B Fc) :
      (Mf.model Fc).neutral.baseChangeUnramified.congruenceSubgroup ≤
        (Mf.model Fd.val).neutral.baseChangeUnramified.integralPoints := by
    let : Smooth (Mf.model Fc).neutral.baseChangeUnramified.group.X.hom :=
      (Mf.model Fc).neutral.isSmooth_baseChange (fixedFieldIntegers F)
        (inertiaFixedField F) (Mf.model Fc).neutral_smooth
    let : ConnectedSpace (Mf.model Fc).neutral.baseChangeUnramified.specialFibre.X.left :=
      (Mf.model Fc).unramifiedNeutral_hasConnectedSpecialFibre
    exact unramifiedModels_congruenceSubgroup_le_of_upstairs_rootGeneration hgen
      B C e a hequiv hap hfacets E Fc Fd.val Fd.property
      (Mf.model Fc).neutral.baseChangeUnramified
      (Mf.model Fd.val).neutral.baseChangeUnramified
      (hmodel Fc) (hmodel Fd.val)
      ((Mf.morphism Fc Fd.val Fd.property).baseChange
        (fixedFieldIntegers F) (inertiaFixedField F)).neutral
  exact Mf.hasUnramifiedIncidentImageEmbedding
    B C E e a hapt hcommon hequiv hap hfacets Fc Q hmodel hker hQ hpar

end IncidentImageEmbedding

/-- The complete order-bijection target follows from the exact upstairs
radical-generation statement, with no additional global premise. -/
def UnramifiedFacetParabolicOrderReductionStatement : Prop :=
  UnramifiedUpstairsRadicalRootGenerationStatement.{u} →
    UnramifiedFacetParabolicOrderStatement.{u}

/-- Combine upper congruence containment and upper parabolicity with actual
quotient-image recovery, arbitrary-facet attainment, and forced composition. -/
theorem unramifiedFacetParabolicOrder_of_upstairs_rootGeneration :
    UnramifiedFacetParabolicOrderReductionStatement.{u} := by
  intro hgen F _ _ _ _ G _ P R T hbuilding hopen haff hroot hapt hfacet htits
    C A e a hinj hequiv hap hfixed hsurj hspecial hfacets hkernel E Mf hmodel Fc Q hQ
  let B := P.toValuationBuildingData
  have hcommon := R.hasCommonApartmentWith_of_isBuilding hbuilding.isBuilding
  obtain ⟨hmaps, hinjective⟩ := unramifiedIncidentImageEmbedding_of_upstairs_rootGeneration
    hgen B C E e a hapt hcommon hequiv hap hfacets Mf (fun Fd => (hmodel Fd).2) Fc Q hQ
  refine ⟨⟨hmaps, hinjective.injOn, ?_⟩, Mf.incidentParabolicImage_le Fc Q⟩
  intro J hJ
  obtain ⟨H, j, hj, rfl⟩ := hJ
  obtain ⟨Fd, hFd⟩ := unramifiedFacetParabolicSurjectivity F G P R T
    hbuilding hopen haff hroot hapt hfacet htits C A e a
    hinj hequiv hap hfixed hsurj hspecial hfacets hkernel E Mf hmodel Fc Q hQ H j hj
  exact ⟨Fd, Set.mem_univ _, hFd⟩

end Langlands.BruhatTits.IntegralModels
