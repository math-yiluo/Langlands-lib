import Langlands.BruhatTits.IntegralModels.UnramifiedFacetImageParabolicity
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetKernel
import Langlands.BruhatTits.IntegralModels.PositiveReductionPreimage
import Langlands.BruhatTits.IntegralModels.SpecialFibreImagePoints
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetParabolicImageStatement
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetPositiveRadicalStatement

/-! # Integral lifting for parabolic images of descended facet models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

namespace RelativeComponentModelHom

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [HenselianLocalRing R]
    [PerfectField (IsLocalRing.ResidueField R)]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {source target : RelativeComponentModelData R K G}
    (φ : RelativeComponentModelHom source target)

attribute [local instance] specialFibre_affine specialFibre_isAffine

/-- The full geometric kernel and the universal reductive-positive containment
give the exact reduction-preimage equality over a Henselian local ring. -/
theorem hasParabolicReductionPreimage_of_unipotentKernel_of_reductivePositivePoints_le
    (hkernel : φ.HasSmoothConnectedUnipotentKernel)
    (hpositive : ∀ (Q : SpecialFibreQuotientData target)
      (Qsource : SpecialFibreQuotientData source),
      Q.IsReductiveQuotient → Qsource.IsReductiveQuotient →
        Q.positivePoints ≤ Qsource.positivePoints) :
    φ.HasParabolicReductionPreimage :=
  φ.hasParabolicReductionPreimage_of_reductivePositivePoints_le
    (φ.specialFibreImageProjection_surjective hkernel) hpositive

/-- A chosen source integral section above a target section reducing into the
actual schematic image, using the full kernel and reductive-positive inputs. -/
def unipotentKernelReductionPreimageLift
    (hkernel : φ.HasSmoothConnectedUnipotentKernel)
    (hpositive : ∀ (Q : SpecialFibreQuotientData target)
      (Qsource : SpecialFibreQuotientData source),
      Q.IsReductiveQuotient → Qsource.IsReductiveQuotient →
        Q.positivePoints ≤ Qsource.positivePoints)
    (x : φ.specialFibreImagePoints.comap target.neutral.reduction) :
    source.neutral.integralSections :=
  Classical.choose
    ((φ.hasParabolicReductionPreimage_of_unipotentKernel_of_reductivePositivePoints_le
      hkernel hpositive).le x.property)

/-- The chosen lift maps to precisely the supplied target integral section. -/
theorem unipotentKernelReductionPreimageLift_spec
    (hkernel : φ.HasSmoothConnectedUnipotentKernel)
    (hpositive : ∀ (Q : SpecialFibreQuotientData target)
      (Qsource : SpecialFibreQuotientData source),
      Q.IsReductiveQuotient → Qsource.IsReductiveQuotient →
        Q.positivePoints ≤ Qsource.positivePoints)
    (x : φ.specialFibreImagePoints.comap target.neutral.reduction) :
    rationalPoints.map φ.neutral.hom
      (φ.unipotentKernelReductionPreimageLift hkernel hpositive x) = x :=
  Classical.choose_spec
    ((φ.hasParabolicReductionPreimage_of_unipotentKernel_of_reductivePositivePoints_le
      hkernel hpositive).le x.property)

end RelativeComponentModelHom

private instance facetParabolicReductionAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- For characterized incident facet models, the full upstairs generation
statement and the two lifting inputs imply both clauses of the target. -/
theorem unramifiedFacetParabolicImage_of_generation_kernel_positive
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
    (φ : RelativeComponentModelHom D' D)
    (hkernel : φ.HasSmoothConnectedUnipotentKernel)
    (hpositive : ∀ (Q : SpecialFibreQuotientData D)
      (Q' : SpecialFibreQuotientData D'),
      Q.IsReductiveQuotient → Q'.IsReductiveQuotient →
        Q.positivePoints ≤ Q'.positivePoints) :
    φ.HasParabolicSpecialFibreImage ∧ φ.HasParabolicReductionPreimage := by
  let : HenselianLocalRing ↥𝒪[F] := henselianLocalRing_integer
  exact ⟨unramifiedFacetImage_isParabolic_of_upstairs_rootGeneration
    hgen B C e a hequiv hap hfac E Fc Fc' hFC D D' hN hN' φ,
    φ.hasParabolicReductionPreimage_of_unipotentKernel_of_reductivePositivePoints_le
      hkernel hpositive⟩

/-- The explicit full-kernel input used by the conditional descended-facet
assembly. This is a proposition, not an asserted kernel theorem. -/
def UnramifiedFacetKernelCriterion : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)
  (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
  (e : B.ReducedBuilding → C.ReducedBuilding)
  (a : B.Apartment →ᵃ[ℝ] C.Apartment),
  (∀ (g : rationalPoints G) (z : B.ReducedBuilding),
    e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z) →
  (∀ x : B.Apartment, e (B.apartmentMap x) = C.apartmentMap (a x)) →
  (∀ x : B.Apartment,
    a ⁻¹' AffineRootSystem.facet C.affineRoots (a x) =
      AffineRootSystem.facet B.affineRoots x) →
  ∀ (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (Fc Fc' : BuildingFacet B),
    FacetPrecedes B Fc Fc' →
  ∀ (D D' : RelativeComponentModelData ↥𝒪[F] F G),
    D.neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val) →
    D'.neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc'.val) →
    ∀ φ : RelativeComponentModelHom D' D,
      φ.HasSmoothConnectedUnipotentKernel

set_option maxHeartbeats 2400000 in
/-- The unchanged full target follows from upstairs generation, the full
positive-radical statement, and an explicit kernel criterion for the same
characterized incident facet models. -/
theorem unramifiedFacetParabolicImage_of_generation_positive_kernelCriterion
    (hgen : UnramifiedUpstairsRadicalRootGenerationStatement.{u})
    (hpositive : UnramifiedFacetPositiveRadicalStatement.{u})
    (hkernel : UnramifiedFacetKernelCriterion.{u}) :
    UnramifiedFacetParabolicImageStatement.{u} := by
  intro F _ _ _ _ G _ P R T hbuilding hbounded hsplit hreflect
    hapartments hcompatible htits C A e a hinj hequiv hap hfixed hsurj
    hspecial hfac htorus E Fc Fc' hFC D D' hD hD' hN hN' φ
  constructor
  · exact unramifiedFacetImage_isParabolic_of_upstairs_rootGeneration hgen
      P.toValuationBuildingData C e a hequiv hap hfac E Fc Fc' hFC D D' hN hN' φ
  · let : HenselianLocalRing ↥𝒪[F] := henselianLocalRing_integer
    apply φ.hasParabolicReductionPreimage_of_unipotentKernel_of_reductivePositivePoints_le
    · exact hkernel F G P.toValuationBuildingData C e a hequiv hap hfac E
        Fc Fc' hFC D D' hN hN' φ
    · exact hpositive F G P R T hbuilding hbounded hsplit hreflect
        hapartments hcompatible htits C A e a hinj hequiv hap hfixed hsurj
        hspecial hfac htorus E Fc Fc' hFC D D' hD hD' hN hN'

/-- The full model-kernel statement supplies the facet-kernel criterion via
the actual common facet chart and residue-field kernel reflection. -/
theorem unramifiedFacetKernelCriterion_of_modelKernel
    (hkernel : UnramifiedModelKernelStatement.{u}) :
    UnramifiedFacetKernelCriterion.{u} := by
  intro F _ _ _ _ G _ B C e a hequiv hap hfac E Fc Fc' hFC D D' hN hN' φ
  exact unramifiedFacetKernel_of_modelKernel B C e a hequiv hap hfac hkernel
    E Fc Fc' hFC D D' hN hN' φ

/-- The unchanged full target is reduced to the three full global statements:
upstairs radical generation, positive-radical monotonicity and model kernels. -/
theorem unramifiedFacetParabolicImage_of_generation_positive_modelKernel
    (hgen : UnramifiedUpstairsRadicalRootGenerationStatement.{u})
    (hpositive : UnramifiedFacetPositiveRadicalStatement.{u})
    (hkernel : UnramifiedModelKernelStatement.{u}) :
    UnramifiedFacetParabolicImageStatement.{u} :=
  unramifiedFacetParabolicImage_of_generation_positive_kernelCriterion hgen
    hpositive (unramifiedFacetKernelCriterion_of_modelKernel hkernel)

end Langlands.BruhatTits.IntegralModels
