import Langlands.BruhatTits.IntegralModels.UnramifiedFacetModelAttainment
import Langlands.BruhatTits.IntegralModels.UnramifiedDescendedFacetRecovery
import Langlands.BruhatTits.IntegralModels.FacetParabolicTransfer
import Langlands.Geometry.Building.BuildingFacetRestrictionOrder

/-! # Actual unramified facet-image order and full downstairs incidence -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.BruhatTits.IntegralModels

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.Geometry.Building.UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
  [IsAffineHom H.X.hom]
  (E : UnramifiedZeroDatum F H) (C : MaximalUnramified.BuildingData F H)
  (ρ : rationalPoints G →* rationalPoints H)
  (e : B.ReducedBuilding → C.ReducedBuilding)
  (a : B.Apartment →ᵃ[ℝ] C.Apartment)
  (hD : B.SatisfiesApartmentAxioms)
  (hcommon : ∀ x : B.ReducedBuilding, B.HasCommonApartmentWith x)
  (hequiv : ∀ (g : rationalPoints G) (x : B.ReducedBuilding),
    e (g • x) = ρ g • e x)
  (hap : ∀ x : B.Apartment, e (B.apartmentMap x) = C.apartmentMap (a x))
  (hfac : ∀ x : B.Apartment,
    a ⁻¹' AffineRootSystem.facet C.affineRoots (a x) =
      AffineRootSystem.facet B.affineRoots x)

include hD hcommon hequiv hap hfac

/-- Under no inversions, full downstairs incidence is exactly reverse
inclusion of the actual zero fixers of the facet images. -/
theorem descendedFacet_precedes_iff_zeroFixer_le
    (hno : MaximalUnramified.ZeroFacetNoInversionsStatement.{u})
    (Fc Fd : BuildingFacet B) :
    FacetPrecedes B Fc Fd ↔
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fd.val) ≤
        E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val) := by
  let j := B.facetRestrictionEmbedding C ρ e a hD hcommon hequiv hap hfac
  have hsubset (Fa : BuildingFacet B) : e '' Fa.val ⊆ (j Fa).val :=
    B.image_subset_facetRestrictionEmbedding C ρ e a hD hcommon hequiv hap hfac Fa
  constructor
  · intro h
    have hup : C.FacetPrecedes (j Fc) (j Fd) :=
      (B.facetRestrictionEmbedding_facetPrecedes_iff
        C ρ e a hD hcommon hequiv hap hfac Fc Fd).mpr h
    rw [E.zeroFixer_eq_of_nonempty_subset_buildingFacet C hno
      (Fd.property.nonempty.image e) (hsubset Fd),
      E.zeroFixer_eq_of_nonempty_subset_buildingFacet C hno
        (Fc.property.nonempty.image e) (hsubset Fc)]
    exact inf_le_inf_left _ (C.pointwiseFixer_le_of_facetPrecedes hup)
  · intro h
    apply (B.facetRestrictionEmbedding_facetPrecedes_iff
      C ρ e a hD hcommon hequiv hap hfac Fc Fd).mp
    exact E.facetPrecedes_of_buildingZeroFixer_le C
      (Fd.property.nonempty.image e) (hsubset Fd)
      (Fc.property.nonempty.image e) (hsubset Fc) h

end Langlands.Geometry.Building.UnramifiedZeroDatum

namespace Langlands.BruhatTits.IntegralModels

open Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
  [IsAffineHom H.X.hom]
  (E : UnramifiedZeroDatum F H) (C : MaximalUnramified.BuildingData F H)
  (ρ : rationalPoints G →* rationalPoints H)
  (e : B.ReducedBuilding → C.ReducedBuilding)
  (a : B.Apartment →ᵃ[ℝ] C.Apartment)
  (hD : B.SatisfiesApartmentAxioms)
  (hcommon : ∀ x : B.ReducedBuilding, B.HasCommonApartmentWith x)
  (hequiv : ∀ (g : rationalPoints G) (x : B.ReducedBuilding),
    e (g • x) = ρ g • e x)
  (hap : ∀ x : B.Apartment, e (B.apartmentMap x) = C.apartmentMap (a x))
  (hfac : ∀ x : B.Apartment,
    a ⁻¹' AffineRootSystem.facet C.affineRoots (a x) =
      AffineRootSystem.facet B.affineRoots x)
  {R : Type u} [CommRing R] [IsDomain R]
  [Algebra R (UnramifiedClosure F)] [IsFractionRing R (UnramifiedClosure F)]
  [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
  {source₁ source₂ target : RelativeComponentModelData R (UnramifiedClosure F) H}
  (φ : RelativeComponentModelHom source₁ target)
  (ψ : RelativeComponentModelHom source₂ target)

include hD hcommon hequiv hap hfac

/-- Actual special-fibre image inclusion on every test scheme is exactly
reverse incidence of the characterized full downstairs facets. -/
theorem unramifiedSpecialFibreImage_le_iff_descendedFacetPrecedes
    (hno : MaximalUnramified.ZeroFacetNoInversionsStatement.{u})
    {Fc Fd : BuildingFacet B}
    (hsource₁ : source₁.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val))
    (hsource₂ : source₂.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fd.val))
    (hker₁ : target.neutral.congruenceSubgroup ≤ source₁.neutral.integralPoints)
    (hker₂ : target.neutral.congruenceSubgroup ≤ source₂.neutral.integralPoints) :
    SubgroupFunctor.range φ.specialFibreImageInclusion ≤
        SubgroupFunctor.range ψ.specialFibreImageInclusion ↔
      FacetPrecedes B Fd Fc := by
  rw [φ.specialFibreImage_le_iff_integralPoints_le ψ hker₁ hker₂,
    hsource₁, hsource₂]
  exact (E.descendedFacet_precedes_iff_zeroFixer_le B C ρ e a
    hD hcommon hequiv hap hfac hno Fd Fc).symm

/-- For parabolic actual special-fibre images, the same order reflection
holds after the actual reductive-quotient projection. -/
theorem unramifiedReductiveImage_le_iff_descendedFacetPrecedes
    (hno : MaximalUnramified.ZeroFacetNoInversionsStatement.{u})
    {Fc Fd : BuildingFacet B}
    (hsource₁ : source₁.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val))
    (hsource₂ : source₂.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (e '' Fd.val))
    (hker₁ : target.neutral.congruenceSubgroup ≤ source₁.neutral.integralPoints)
    (hker₂ : target.neutral.congruenceSubgroup ≤ source₂.neutral.integralPoints)
    (Q : SpecialFibreQuotientData target) (hQ : Q.IsReductiveQuotient)
    (hφ : φ.HasParabolicSpecialFibreImage)
    (hψ : ψ.HasParabolicSpecialFibreImage) :
    SubgroupFunctor.range (φ.reductiveImageInclusion Q) ≤
        SubgroupFunctor.range (ψ.reductiveImageInclusion Q) ↔
      FacetPrecedes B Fd Fc := by
  obtain ⟨hφq, hφc⟩ := φ.parabolicReductiveImage_and_comap Q hQ hφ
  obtain ⟨hψq, hψc⟩ := ψ.parabolicReductiveImage_and_comap Q hQ hψ
  let Pφ : ParabolicFunctor Q.quotient :=
    ⟨SubgroupFunctor.range (φ.reductiveImageInclusion Q),
      ⟨φ.reductiveImage Q, φ.reductiveImageInclusion Q, hφq, rfl⟩⟩
  let Pψ : ParabolicFunctor Q.quotient :=
    ⟨SubgroupFunctor.range (ψ.reductiveImageInclusion Q),
      ⟨ψ.reductiveImage Q, ψ.reductiveImageInclusion Q, hψq, rfl⟩⟩
  have hord := (Q.parabolicComapOrderIso hQ).le_iff_le (x := Pφ) (y := Pψ)
  change (SubgroupFunctor.range (φ.reductiveImageInclusion Q)).comap Q.projection ≤
      (SubgroupFunctor.range (ψ.reductiveImageInclusion Q)).comap Q.projection ↔
    SubgroupFunctor.range (φ.reductiveImageInclusion Q) ≤
      SubgroupFunctor.range (ψ.reductiveImageInclusion Q) at hord
  rw [hφc, hψc] at hord
  exact hord.symm.trans
    (unramifiedSpecialFibreImage_le_iff_descendedFacetPrecedes
      B E C ρ e a hD hcommon hequiv hap hfac φ ψ hno
      hsource₁ hsource₂ hker₁ hker₂)

/-- The conditional actual image-order conclusion, with source models,
congruence containments and special-fibre parabolicity kept explicit. -/
def HasDescendedFacetImageOrder (Q : SpecialFibreQuotientData target) : Prop :=
  MaximalUnramified.ZeroFacetNoInversionsStatement.{u} →
    ∀ (Fc Fd : BuildingFacet B),
      source₁.neutral.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val) →
      source₂.neutral.integralPoints =
        E.zeroPoints ⊓ C.pointwiseFixer (e '' Fd.val) →
      target.neutral.congruenceSubgroup ≤ source₁.neutral.integralPoints →
      target.neutral.congruenceSubgroup ≤ source₂.neutral.integralPoints →
      (SubgroupFunctor.range φ.specialFibreImageInclusion ≤
          SubgroupFunctor.range ψ.specialFibreImageInclusion ↔
        FacetPrecedes B Fd Fc) ∧
      (Q.IsReductiveQuotient → φ.HasParabolicSpecialFibreImage →
        ψ.HasParabolicSpecialFibreImage →
        (SubgroupFunctor.range (φ.reductiveImageInclusion Q) ≤
            SubgroupFunctor.range (ψ.reductiveImageInclusion Q) ↔
          FacetPrecedes B Fd Fc))

theorem hasDescendedFacetImageOrder (Q : SpecialFibreQuotientData target) :
    HasDescendedFacetImageOrder B E C e φ ψ Q := by
  intro hno Fc Fd hsource₁ hsource₂ hker₁ hker₂
  exact ⟨unramifiedSpecialFibreImage_le_iff_descendedFacetPrecedes
      B E C ρ e a hD hcommon hequiv hap hfac φ ψ hno
      hsource₁ hsource₂ hker₁ hker₂,
    fun hQ hφ hψ => unramifiedReductiveImage_le_iff_descendedFacetPrecedes
      B E C ρ e a hD hcommon hequiv hap hfac φ ψ hno
      hsource₁ hsource₂ hker₁ hker₂ Q hQ hφ hψ⟩

end Langlands.BruhatTits.IntegralModels
