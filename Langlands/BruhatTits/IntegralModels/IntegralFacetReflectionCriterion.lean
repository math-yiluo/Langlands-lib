import Langlands.BruhatTits.IntegralModels.UnramifiedFacetReflections
import Langlands.Geometry.Building.GenericApartmentInjection
import Langlands.Geometry.Building.AffineSimpleFixedAdmissible

/-! # Detecting facet hyperplanes from integral reflection representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

private instance extensionAffineHom :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

variable
  (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
  (e : P.ReducedBuilding → C.ReducedBuilding) (hinj : Function.Injective e)
  (he : ∀ (g : rationalPoints G) (z : P.ReducedBuilding),
    e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
  (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
  (g : rationalPoints G) (Fa : Set P.Apartment)
  (D : RelativeComponentModelData ↥𝒪[F] F G)
  (hD : D.neutral.baseChangeUnramified.integralPoints =
    E.zeroPoints ⊓ C.pointwiseFixer
      (e '' (P.translatedApartmentMap g '' Fa)))

include hinj he hD

/-- For a simply connected image normalizer, integral membership is equivalent
to fixing the apartment subset, provided the building comparison is injective. -/
theorem conjugated_normalizer_mem_integralPoints_iff
    (n : normalizerPoints P.i)
    (hsc : (n : rationalPoints G) ∈ P.simplyConnectedImage) :
    rationalPoints.map (G.innerIso g).hom n ∈ D.neutral.integralPoints ↔
      ∀ y ∈ Fa, n • y = y := by
  constructor
  · intro hn y hy
    have hnK :=
      (D.neutral.mem_integralPoints_rationalExtend_iff_unramified _).mpr hn
    rw [hD] at hnK
    have hfix := C.apartment.mem_pointwiseFixer.mp hnK.2
      (e (P.translatedApartmentMap g y)) ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [← he] at hfix
    have hfixF := hinj hfix
    change (n.val ≫ (G.innerIso g).hom.hom.hom) •
      (g • P.apartmentMap y) = g • P.apartmentMap y at hfixF
    rw [comp_innerIso_hom, constantPoint_self, mul_smul, mul_smul,
      inv_smul_smul, P.normalizer_smul_apartmentMap n] at hfixF
    exact P.apartment.apartmentMap_injective P.isConnectedReductive
      P.isMaximalSplitTorus (MulAction.injective g hfixF)
  · exact conjugated_normalizer_mem_integralPoints P C e he E g Fa D hD n hsc

variable (hA : P.SatisfiesApartmentAxioms) (hR : P.HasRootReflections)
  {a : relativeRoots P.i} {u : rationalPoints G}
  {p : rationalPoints G × rationalPoints G}

include hA hR

/-- An actual opposite-pair reflection is integral exactly when its valuation
functional vanishes identically on the apartment subset. -/
theorem conjugated_reflection_mem_integralPoints_iff
    (hu : u ∈ P.rootGroup a) (hu1 : u ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair P.i a.val u p) :
    rationalPoints.map (G.innerIso g).hom (P.reflectionElement hp) ∈
        D.neutral.integralPoints ↔
      ∀ y ∈ Fa, P.reflectionFunctional a u y = 0 := by
  rw [conjugated_normalizer_mem_integralPoints_iff P C e hinj he E g Fa D hD
    (P.reflectionElement hp) (P.reflectionElement_mem_simplyConnectedImage hA hu hu1 hp)]
  apply forall_congr'
  intro y
  apply forall_congr'
  intro _
  change P.apartment.normalizerAffineEquiv (P.reflectionElement hp) y = y ↔ _
  rw [P.toValuationBuildingData.normalizerAffineEquiv_reflectionElement_of_hasRootReflections
    hR hu hu1 hp]
  exact AffineRootSystem.affineReflection_apply_eq_self_iff _ _ _

/-- If its valuation functional is an ordinary affine root, an integral actual
reflection certifies the precise generic derivative root. -/
theorem mem_facetDerivativeRoots_of_integral_reflection
    (hu : u ∈ P.rootGroup a) (hu1 : u ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair P.i a.val u p)
    (hordinary : P.reflectionFunctional a u ∈ P.affineRoots)
    (hint : rationalPoints.map (G.innerIso g).hom (P.reflectionElement hp) ∈
      D.neutral.integralPoints) :
    a.val ∈ facetDerivativeRoots P.toValuationBuildingData Fa :=
  ⟨a.property, P.reflectionFunctional a u, hordinary,
    P.reflectionFunctional_linear a u,
    (conjugated_reflection_mem_integralPoints_iff P C e hinj he E g Fa D hD hA hR
      hu hu1 hp).mp hint⟩

/-- An integral actual reflection supplies an ordinary affine root vanishing on
the subset. Its functional is the point functional itself or twice it. -/
def ordinaryFacetRootOfIntegralReflection
    (hu : u ∈ P.rootGroup a) (hu1 : u ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair P.i a.val u p)
    (hint : rationalPoints.map (G.innerIso g).hom (P.reflectionElement hp) ∈
      D.neutral.integralPoints) :
    {ψ : P.Apartment →ᵃ[ℝ] ℝ //
      ψ ∈ P.affineRoots ∧
      (ψ = P.reflectionFunctional a u ∨ ψ = (2 : ℝ) • P.reflectionFunctional a u) ∧
      ∀ y ∈ Fa, ψ y = 0} := by
  apply Classical.choice
  have hzero :=
    (conjugated_reflection_mem_integralPoints_iff P C e hinj he E g Fa D hD hA hR
      hu hu1 hp).mp hint
  have hext : P.reflectionFunctional a u ∈ P.apartment.extendedAffineRoots := by
    rw [← P.toValuationBuildingData.reflectionAffineRoots_eq]
    exact ⟨a, u, hu, hu1, rfl⟩
  rcases hA.mem_or_two_smul_mem _ hext with hψ | hψ
  · exact ⟨⟨_, hψ, Or.inl rfl, hzero⟩⟩
  · refine ⟨⟨_, hψ, Or.inr rfl, fun y hy => ?_⟩⟩
    change (2 : ℝ) * P.reflectionFunctional a u y = 0
    rw [hzero y hy, mul_zero]

end Langlands.BruhatTits.IntegralModels
