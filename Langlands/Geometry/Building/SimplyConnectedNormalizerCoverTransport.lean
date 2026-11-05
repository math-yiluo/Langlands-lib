import Langlands.Geometry.Building.SimplyConnectedApartmentWeylAction
import Langlands.Geometry.Building.SimplyConnectedNormalizerAffineWeylReduction
import Langlands.Geometry.Building.AffineRootSystemTransport

/-! # Transport from a simply connected apartment to the actual normalizer image -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G C : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffineHom C.X.hom]
    (P : ParahoricBuildingData G) (B : ValuationBuildingData C)
    (f : normalizerPoints B.i →* normalizerPoints P.i)
    (e : B.Apartment ≃ᵃ[ℝ] P.Apartment)

/-- Actual apartment equivariance identifies the original affine actions under
affine conjugation. -/
theorem affineConjugation_normalizerAffineEquiv_of_equivariant
    (he : ∀ (m : normalizerPoints B.i) (x : B.Apartment), e (m • x) = f m • e x)
    (m : normalizerPoints B.i) :
    AffineRootSystem.affineConjugation e (B.apartment.normalizerAffineEquiv m) =
      P.apartment.normalizerAffineEquiv (f m) := by
  apply AffineEquiv.ext
  intro x
  change e (m • e.symm x) = f m • x
  rw [he, e.apply_symm_apply]

/-- Root transport and lifts of the actual normalizer intersection transfer the
simply connected upper inclusion. The target AS 3 condition supplies source AS 3;
no AS 5 or complete apartment axioms for the source are assumed. -/
theorem simplyConnectedNormalizer_map_le_affineWeylGroup_of_comparison
    (hroots : AffineRootSystem.transportedRoots e B.affineRoots = P.affineRoots)
    (he : ∀ (m : normalizerPoints B.i) (x : B.Apartment), e (m • x) = f m • e x)
    (hlift : ∀ n ∈ P.simplyConnectedImage.subgroupOf (normalizerPoints P.i),
      ∃ m : normalizerPoints B.i, f m = n)
    (hfix : SimplyConnectedFacetFixingStatement.{u}) (hsc : IsSimplyConnected C)
    (hFB : RelativeRoot.HasOppositeFactorPairs B.i)
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero P.affineRoots) :
    (P.simplyConnectedImage.subgroupOf (normalizerPoints P.i)).map
        P.apartment.normalizerAffineEquiv ≤
      AffineRootSystem.affineWeylGroup P.affineRoots := by
  have hΨB : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots := by
    have ht := hΨ.transport e.symm
    rwa [← hroots, AffineRootSystem.transportedRoots_symm] at ht
  rintro _ ⟨n, hn, rfl⟩
  obtain ⟨m, hm⟩ := hlift n hn
  have hw : B.apartment.normalizerAffineEquiv m ∈
      AffineRootSystem.affineWeylGroup B.affineRoots := by
    rw [← B.normalizerAffineEquiv_range_eq_affineWeylGroup_of_simplyConnectedFacetFixing
      hfix hsc hΨB hFB]
    exact ⟨m, rfl⟩
  have hmap :
      AffineRootSystem.affineConjugation e (B.apartment.normalizerAffineEquiv m) ∈
        (AffineRootSystem.affineWeylGroup B.affineRoots).map
          (AffineRootSystem.affineConjugation e).toMonoidHom :=
    ⟨B.apartment.normalizerAffineEquiv m, hw, rfl⟩
  rw [AffineRootSystem.map_affineWeylGroup_of_transportedRoots_eq e hroots,
    P.affineConjugation_normalizerAffineEquiv_of_equivariant B f e he, hm] at hmap
  exact hmap

/-- Under explicit actual source comparisons and opposite-pair existence, the
normalizer intersection has exactly the affine Weyl image. -/
theorem simplyConnectedNormalizer_map_eq_affineWeylGroup_of_comparison
    (hroots : AffineRootSystem.transportedRoots e B.affineRoots = P.affineRoots)
    (he : ∀ (m : normalizerPoints B.i) (x : B.Apartment), e (m • x) = f m • e x)
    (hlift : ∀ n ∈ P.simplyConnectedImage.subgroupOf (normalizerPoints P.i),
      ∃ m : normalizerPoints B.i, f m = n)
    (hfix : SimplyConnectedFacetFixingStatement.{u}) (hsc : IsSimplyConnected C)
    (hFB : RelativeRoot.HasOppositeFactorPairs B.i)
    (hA : P.SatisfiesApartmentAxioms)
    (hFP : RelativeRoot.HasOppositeFactorPairs P.i) :
    (P.simplyConnectedImage.subgroupOf (normalizerPoints P.i)).map
        P.apartment.normalizerAffineEquiv =
      AffineRootSystem.affineWeylGroup P.affineRoots :=
  le_antisymm
    (P.simplyConnectedNormalizer_map_le_affineWeylGroup_of_comparison
      B f e hroots he hlift hfix hsc hFB hA.isAffineRootSystem_affineRoots)
    (P.affineWeylGroup_le_simplyConnectedNormalizer_map_of_exists_oppositePairs hA hFP)

/-- Restrict the original action of `N(F) ∩ G(F)^♮` to the affine Weyl subgroup
using explicit comparisons with a simply connected source apartment. -/
def simplyConnectedImageNormalizerWeylActionOfComparison
    (hroots : AffineRootSystem.transportedRoots e B.affineRoots = P.affineRoots)
    (he : ∀ (m : normalizerPoints B.i) (x : B.Apartment), e (m • x) = f m • e x)
    (hlift : ∀ n ∈ P.simplyConnectedImage.subgroupOf (normalizerPoints P.i),
      ∃ m : normalizerPoints B.i, f m = n)
    (hfix : SimplyConnectedFacetFixingStatement.{u}) (hsc : IsSimplyConnected C)
    (hFB : RelativeRoot.HasOppositeFactorPairs B.i)
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero P.affineRoots) :
    P.simplyConnectedImage.subgroupOf (normalizerPoints P.i) →*
      AffineRootSystem.affineWeylGroup P.affineRoots where
  toFun n := ⟨P.apartment.normalizerAffineEquiv n,
    P.simplyConnectedNormalizer_map_le_affineWeylGroup_of_comparison
      B f e hroots he hlift hfix hsc hFB hΨ ⟨n, n.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one P.apartment.normalizerAffineEquiv)
  map_mul' n m := Subtype.ext (map_mul P.apartment.normalizerAffineEquiv
    (n : normalizerPoints P.i) (m : normalizerPoints P.i))

@[simp]
theorem simplyConnectedImageNormalizerWeylActionOfComparison_coe
    (hroots : AffineRootSystem.transportedRoots e B.affineRoots = P.affineRoots)
    (he : ∀ (m : normalizerPoints B.i) (x : B.Apartment), e (m • x) = f m • e x)
    (hlift : ∀ n ∈ P.simplyConnectedImage.subgroupOf (normalizerPoints P.i),
      ∃ m : normalizerPoints B.i, f m = n)
    (hfix : SimplyConnectedFacetFixingStatement.{u}) (hsc : IsSimplyConnected C)
    (hFB : RelativeRoot.HasOppositeFactorPairs B.i)
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero P.affineRoots)
    (n : P.simplyConnectedImage.subgroupOf (normalizerPoints P.i)) :
    (P.simplyConnectedImageNormalizerWeylActionOfComparison
        B f e hroots he hlift hfix hsc hFB hΨ n : P.Apartment ≃ᵃ[ℝ] P.Apartment) =
      P.apartment.normalizerAffineEquiv n :=
  rfl

/-- The restricted original action reaches every affine Weyl element, using
actual target reflections for surjectivity. -/
theorem simplyConnectedImageNormalizerWeylActionOfComparison_surjective
    (hroots : AffineRootSystem.transportedRoots e B.affineRoots = P.affineRoots)
    (he : ∀ (m : normalizerPoints B.i) (x : B.Apartment), e (m • x) = f m • e x)
    (hlift : ∀ n ∈ P.simplyConnectedImage.subgroupOf (normalizerPoints P.i),
      ∃ m : normalizerPoints B.i, f m = n)
    (hfix : SimplyConnectedFacetFixingStatement.{u}) (hsc : IsSimplyConnected C)
    (hFB : RelativeRoot.HasOppositeFactorPairs B.i)
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero P.affineRoots)
    (hA : P.SatisfiesApartmentAxioms)
    (hFP : RelativeRoot.HasOppositeFactorPairs P.i) :
    Function.Surjective (P.simplyConnectedImageNormalizerWeylActionOfComparison
      B f e hroots he hlift hfix hsc hFB hΨ) := by
  intro w
  obtain ⟨n, hn, heq⟩ :=
    P.affineWeylGroup_le_simplyConnectedNormalizer_map_of_exists_oppositePairs
      hA hFP w.property
  exact ⟨⟨n, hn⟩, Subtype.ext heq⟩

end Langlands.Geometry.Building.ParahoricBuildingData
