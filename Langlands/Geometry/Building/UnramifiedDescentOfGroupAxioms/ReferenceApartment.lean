import Langlands.Geometry.Building.UnramifiedApartmentDescentReduction
import Langlands.Geometry.Building.UnramifiedAffineRootRestrictionProof
import Langlands.Geometry.Building.UnramifiedGaloisFixedBuildingPointProof
import Langlands.Geometry.Building.UnramifiedValuationDescentProof

/-! # Descent with a prescribed special reference apartment -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.UnramifiedBuildingDescent

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local notation "K" => inertiaFixedField F
local notation "G_K" => baseChanged F K G
local notation "b" => algebraBaseMap F K

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- Apartment-compatible building descent with the specified upper building and
coefficient action, including the range and affine roots of the apartment map. -/
structure ReferenceApartmentDescent (B : ValuationBuildingData G)
    (C : MaximalUnramified.BuildingData F G_K)
    (Γ : MaximalUnramified.SemilinearApartmentData (G := G) C) where
  embedding : B.ReducedBuilding → C.ReducedBuilding
  apartment : B.Apartment →ᵃ[ℝ] C.Apartment
  injective : Function.Injective embedding
  equivariant : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
    embedding (g • z) = rationalExtend F K G g • embedding z
  apartment_compatible : ∀ w : B.Apartment,
    embedding (B.apartmentMap w) = C.apartmentMap (apartment w)
  fixed : ∀ (σ : K ≃ₐ[F] K) (z : B.ReducedBuilding),
    Γ.action σ (embedding z) = embedding z
  surjective_fixed : ∀ y : C.ReducedBuilding,
    (∀ σ : K ≃ₐ[F] K, Γ.action σ y = y) → ∃ z, embedding z = y
  special : ∀ z : B.ReducedBuilding, C.IsSpecialPoint (embedding z) → B.IsSpecialPoint z
  roots : AffineRootSystem.restrictedRoots apartment C.affineRoots = B.affineRoots
  torus_units : ∀ w : B.Apartment,
    IsFixedByUnramifiedTorusUnits F B.i (embedding (B.apartmentMap w))
  apartment_injective : Function.Injective apartment
  apartment_range : Set.range apartment =
    {y | ∀ σ : K ≃ₐ[F] K, Γ.action σ (C.apartmentMap y) = C.apartmentMap y}

set_option maxHeartbeats 5000000 in
/-- Carry out apartment-compatible building descent with a prescribed special
`F`-torus and a specified compatible valuation apartment over `K`. -/
theorem referenceApartmentDescent (B : ValuationBuildingData G)
    (hB : ∃ R : B.PolysimplicialRealization, B.SatisfiesBuildingAxiom R)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (iT : T.toGrp ⟶ G)
    (f : B.S ⟶ T) (hf : CommGroupScheme.groupHom f ≫ iT = B.i)
    (hGK : IsConnectedReductive G_K)
    (hiT : IsMaximalSplitTorus (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map iT))
    [Mono ((GroupScheme.baseChange b).map iT).hom.hom.left]
    (A : KPApartmentData (S := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map iT) (IntegerValuation.order (MaximalUnramified.valuation F)))
    (Z : CentralizerDatum (S := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map iT))
    (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) A Z)
    (hA : KPApartmentData.GaloisStable F K iT A) :
    Nonempty (ReferenceApartmentDescent B (buildingData iT hGK hiT A Z h6)
      (semilinearData iT hGK hiT Z h6 hA)) := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  have hE : RelativeRoot.HasOppositeFactorPairs
      (T := (CommGroupScheme.baseChange b).obj T) ((GroupScheme.baseChange b).map iT) :=
    (RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs _ hiT.isSplitSubtorus.1).mp
      (rootRankOneFactorization K G_K hGK _ _ hiT)
  obtain ⟨A₀, Z₀, h6₀, hcar, hinj, hnorm⟩ := unramifiedValuationDescent F G B.isConnectedReductive
    B.S B.i B.isMaximalSplitTorus T iT f hf hiT hE A Z h6
  have hA₀ : A₀ = B.apartment :=
    omegaCompatibleApartmentUniqueness F G B.isConnectedReductive B.S B.i B.isMaximalSplitTorus
      B.centralizer A₀ B.apartment (h6₀.of_centralizerDatum B.centralizer) B.isOmegaCompatible
  subst hA₀
  have hroots := descentAffineMap_roots_of_unramifiedAffineRootRestriction
    hiT hE A B f hcar hinj hf Z h6 unramifiedAffineRootRestriction
  let H := apartmentDescentData hiT hE A B f hcar hinj hroots hGK Z h6 hA hf hnorm
    (fun x w hw a => filtration_le_comap_sharpFixer_of_torusFieldRestriction f hf
      B.isMaximalSplitTorus.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE A x B.apartment w hw a)
    (maximalUnramifiedApartmentInjective F G_K (buildingData iT hGK hiT A Z h6))
    hB (unramifiedGaloisFixedBuildingPoint F G B.isConnectedReductive B.S B.i
      B.isMaximalSplitTorus T iT f hf hiT A Z h6 hA)
  refine ⟨⟨H.embedding, H.apartment, H.injective, H.equivariant, H.apartment_compatible,
    H.fixed, H.surjective_fixed, H.special, hroots, fun w s hs => H.torus_units s hs w,
    descentAffineMap_injective hiT hE A B f hcar hinj, ?_⟩⟩
  ext x
  constructor
  · rintro ⟨w, rfl⟩ σ
    change H.semilinear.action σ (H.building.apartmentMap (H.apartment w)) =
      H.building.apartmentMap (H.apartment w)
    rw [← H.apartment_compatible]
    exact H.fixed σ _
  · intro hx
    have hx' : apartmentGaloisFixed A x := by
      intro σ
      have hσ := hx σ
      change (semilinearData iT hGK hiT Z h6 hA).action σ (A.apartmentMap x) =
        A.apartmentMap x at hσ
      rw [semilinearData_action_apply, KPApartmentData.galoisQuotientAction_apartmentMap] at hσ
      have h := (maximalUnramifiedApartmentInjective F G_K
        (buildingData iT hGK hiT A Z h6)) hσ
      exact congrArg KPApartmentData.Apartment.val h
    let w : B.Apartment := ⟨apartmentRestriction hiT hE A B f x,
      (hcar _).mpr ⟨x, hx', rfl⟩⟩
    exact ⟨w, descentPoint_eq B (apartmentGaloisFixed A) (apartmentRestriction hiT hE A B f)
      hcar hinj hx' w rfl⟩

end Langlands.Geometry.Building.UnramifiedBuildingDescent
