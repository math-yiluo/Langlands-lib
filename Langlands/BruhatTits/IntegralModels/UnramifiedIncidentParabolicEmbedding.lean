import Langlands.BruhatTits.IntegralModels.UnramifiedFacetImageOrderDescent
import Langlands.BruhatTits.IntegralModels.UnramifiedDescendedFacetRecovery

/-! # Recovering incident facets from descended quotient images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)
  (C : MaximalUnramified.BuildingData F
    (GaloisPointComparison.baseChanged F (inertiaFixedField F) G))
  (E : UnramifiedZeroDatum F
    (GaloisPointComparison.baseChanged F (inertiaFixedField F) G))
  (e : B.ReducedBuilding → C.ReducedBuilding)
  (a : B.Apartment →ᵃ[ℝ] C.Apartment)
  (hD : B.SatisfiesApartmentAxioms)
  (hcommon : ∀ x : B.ReducedBuilding, B.HasCommonApartmentWith x)
  (hequiv : ∀ (g : rationalPoints G) (x : B.ReducedBuilding),
    e (g • x) = GaloisPointComparison.rationalExtend F (inertiaFixedField F) G g • e x)
  (hap : ∀ x : B.Apartment, e (B.apartmentMap x) = C.apartmentMap (a x))
  (hfac : ∀ x : B.Apartment,
    a ⁻¹' AffineRootSystem.facet C.affineRoots (a x) =
      AffineRootSystem.facet B.affineRoots x)

private instance incidentEmbedding_affine :
    IsAffineHom (GaloisPointComparison.baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (GaloisPointComparison.baseMap F _))
  infer_instance

local instance incidentEmbeddingIntegerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance incidentEmbeddingIntegerTower : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance incidentEmbeddingIntegerLocal : IsLocalHom (algebraMap ↥𝒪[F] (fixedFieldIntegers F)) :=
  Valuation.HasExtension.instIsLocalHomValuationInteger
    (vR := ValuativeRel.valuation F) (vS := fixedFieldValuation F)

local instance incidentEmbeddingHenselian : HenselianLocalRing (fixedFieldIntegers F) :=
  fixedFieldIntegersIsHenselian F

local instance incidentEmbeddingResidueClosed : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).1

local instance incidentEmbeddingResidueSeparable : Algebra.IsSeparable (IsLocalRing.ResidueField ↥𝒪[F])
    (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
  unramifiedResidue_isSeparable

include hD hcommon hequiv hap hfac in
/-- Equality of the original actual quotient images recovers full downstairs
facets from their unramified characterizations, without a no-inversions premise. -/
theorem descendedFacet_eq_of_unramifiedReductiveImage_eq
    {source₁ source₂ target : RelativeComponentModelData ↥𝒪[F] F G}
    (φ : RelativeComponentModelHom source₁ target)
    (ψ : RelativeComponentModelHom source₂ target)
    (Q : SpecialFibreQuotientData target)
    {Fc Fd : BuildingFacet B}
    (hsource₁ : source₁.neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val))
    (hsource₂ : source₂.neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fd.val))
    (hker₁ : target.neutral.baseChangeUnramified.congruenceSubgroup ≤
      source₁.neutral.baseChangeUnramified.integralPoints)
    (hker₂ : target.neutral.baseChangeUnramified.congruenceSubgroup ≤
      source₂.neutral.baseChangeUnramified.integralPoints)
    (hQ : Q.IsReductiveQuotient)
    (hφ : (φ.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).HasParabolicSpecialFibreImage)
    (hψ : (ψ.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).HasParabolicSpecialFibreImage)
    (heq : SubgroupFunctor.range (φ.reductiveImageInclusion Q) =
      SubgroupFunctor.range (ψ.reductiveImageInclusion Q)) :
    Fc = Fd := by
  have heqbc := (φ.reductiveImage_eq_iff_baseChange
    (fixedFieldIntegers F) (inertiaFixedField F) ψ Q).mp heq
  have hQbc := Q.isReductiveQuotient_baseChange
    (fixedFieldIntegers F) (inertiaFixedField F) hQ
  have himg :
      SubgroupFunctor.range
          (φ.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).specialFibreImageInclusion =
        SubgroupFunctor.range
          (ψ.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).specialFibreImageInclusion := by
    rw [← ((φ.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).parabolicReductiveImage_and_comap
        (Q.baseChange (fixedFieldIntegers F) (inertiaFixedField F)) hQbc hφ).2,
      ← ((ψ.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).parabolicReductiveImage_and_comap
        (Q.baseChange (fixedFieldIntegers F) (inertiaFixedField F)) hQbc hψ).2,
      heqbc]
  exact descendedFacet_eq_of_unramifiedSpecialFibreImage_eq
    B E C (GaloisPointComparison.rationalExtend F (inertiaFixedField F) G)
    e a hD hcommon hequiv hap hfac
    (φ.baseChange (fixedFieldIntegers F) (inertiaFixedField F))
    (ψ.baseChange (fixedFieldIntegers F) (inertiaFixedField F))
    hsource₁ hsource₂ hker₁ hker₂ himg

namespace FacetModelData

variable (M : FacetModelData B ↥𝒪[F]) (Fc : BuildingFacet B)
  (Q : SpecialFibreQuotientData (M.model Fc))

/-- Explicit upstairs inputs ensuring parabolicity and recovery for a
supplied family, without asserting attainment of every parabolic. -/
def HasUnramifiedIncidentImageEmbedding : Prop :=
  (∀ Fd : BuildingFacet B,
    (M.model Fd).neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fd.val)) →
  (∀ Fd : IncidentFacets B Fc,
    (M.model Fc).neutral.baseChangeUnramified.congruenceSubgroup ≤
      (M.model Fd.val).neutral.baseChangeUnramified.integralPoints) →
  Q.IsReductiveQuotient →
  (∀ Fd : IncidentFacets B Fc,
    ((M.morphism Fc Fd.val Fd.property).baseChange
      (fixedFieldIntegers F) (inertiaFixedField F)).HasParabolicSpecialFibreImage) →
  Set.MapsTo (M.incidentParabolicImage Fc Q) Set.univ {P | IsParabolicFunctor P} ∧
    Function.Injective (M.incidentParabolicImage Fc Q)

include hD hcommon hequiv hap hfac in
/-- The actual original quotient-image map of incident facets is injective
and takes values in parabolics under the displayed upstairs inputs. -/
theorem hasUnramifiedIncidentImageEmbedding :
    M.HasUnramifiedIncidentImageEmbedding B C E e Fc Q := by
  intro hsource hker hQ hpar
  constructor
  · intro Fd _
    let φ := M.morphism Fc Fd.val Fd.property
    exact ⟨φ.reductiveImage Q, φ.reductiveImageInclusion Q,
      hasParabolicReductiveImage_of_unramifiedSpecialFibre φ Q hQ (hpar Fd), rfl⟩
  · intro Fd Fd' heq
    apply Subtype.ext
    exact descendedFacet_eq_of_unramifiedReductiveImage_eq
      B C E e a hD hcommon hequiv hap hfac
      (M.morphism Fc Fd.val Fd.property)
      (M.morphism Fc Fd'.val Fd'.property) Q
      (hsource Fd.val) (hsource Fd'.val) (hker Fd) (hker Fd')
      hQ (hpar Fd) (hpar Fd') heq

end FacetModelData
end Langlands.BruhatTits.IntegralModels
