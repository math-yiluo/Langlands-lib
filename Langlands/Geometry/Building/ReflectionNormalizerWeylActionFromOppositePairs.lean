import Langlands.Geometry.Building.AffineRootDoubling
import Langlands.Geometry.Building.ReflectionNormalizerWeylAction

/-! # The actual reflection-normalizer Weyl action from opposite-pair existence -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)
    (hF : RelativeRoot.HasOppositeFactorPairs B.i)

include hF

/-- The supplied reductivity and split torus turn opposite-pair existence into AS4. -/
theorem affineRoot_mem_or_two_smul_mem_of_oppositePairs :
    ∀ ψ ∈ B.apartment.extendedAffineRoots,
      ψ ∈ B.affineRoots ∨ (2 : ℝ) • ψ ∈ B.affineRoots := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  intro ψ hψ
  exact B.apartment.mem_or_two_smul_mem_affineRoots_of_oppositePairs
    B.isMaximalSplitTorus.isSplitSubtorus.1 hF hψ

/-- The actual reflection-generated normalizer acts in the affine Weyl group
from opposite-pair existence, with no explicit apartment-axiom premise. -/
def reflectionWeylActionOfOppositePairs :
    B.reflectionNormalizer →* AffineRootSystem.affineWeylGroup B.affineRoots :=
  B.reflectionWeylActionOfAS4 (B.affineRoot_mem_or_two_smul_mem_of_oppositePairs hF)

@[simp]
theorem reflectionWeylActionOfOppositePairs_coe (n : B.reflectionNormalizer) :
    (B.reflectionWeylActionOfOppositePairs hF n : B.Apartment ≃ᵃ[ℝ] B.Apartment) =
      B.apartment.normalizerAffineEquiv n.val :=
  rfl

@[simp]
theorem reflectionWeylActionOfOppositePairs_apply
    (n : B.reflectionNormalizer) (x : B.Apartment) :
    (B.reflectionWeylActionOfOppositePairs hF n : B.Apartment ≃ᵃ[ℝ] B.Apartment) x =
      n.val • x :=
  rfl

/-- Local reflection-arrangement geometry and opposite-pair existence identify
the reflection-generated image with the whole affine Weyl group. -/
theorem reflectionNormalizer_map_eq_affineWeylGroup_of_oppositePairs
    (hΨ : AffineRootSystem.IsLocallyFiniteReflectionArrangement B.affineRoots) :
    B.reflectionNormalizer.map B.apartment.normalizerAffineEquiv =
      AffineRootSystem.affineWeylGroup B.affineRoots :=
  B.reflectionNormalizer_map_eq_affineWeylGroup_of_AS4
    (B.affineRoot_mem_or_two_smul_mem_of_oppositePairs hF) hΨ hF

theorem reflectionWeylActionOfOppositePairs_surjective
    (hΨ : AffineRootSystem.IsLocallyFiniteReflectionArrangement B.affineRoots) :
    Function.Surjective (B.reflectionWeylActionOfOppositePairs hF) :=
  B.reflectionWeylActionOfAS4_surjective
    (B.affineRoot_mem_or_two_smul_mem_of_oppositePairs hF) hΨ hF

/-- The actual Weyl preimage consists of the reflection subgroup joined with
the kernel, without a full-normalizer generation assumption. -/
theorem comap_affineWeylGroup_eq_reflectionNormalizer_sup_ker_of_oppositePairs
    (hΨ : AffineRootSystem.IsLocallyFiniteReflectionArrangement B.affineRoots) :
    (AffineRootSystem.affineWeylGroup B.affineRoots).comap
        B.apartment.normalizerAffineEquiv =
      B.reflectionNormalizer ⊔ B.apartment.normalizerAffineEquiv.ker :=
  B.comap_affineWeylGroup_eq_reflectionNormalizer_sup_ker_of_AS4
    (B.affineRoot_mem_or_two_smul_mem_of_oppositePairs hF) hΨ hF

/-- Every reflection-normalizer element preserving a facet fixes it pointwise. -/
theorem reflectionNormalizer_facet_fixing_of_oppositePairs
    (hΨ : AffineRootSystem.IsLocallyFiniteReflectionArrangement B.affineRoots)
    {Fa : Set B.Apartment} (hFa : AffineRootSystem.IsFacet B.affineRoots Fa)
    (n : B.reflectionNormalizer) (hfix : (fun x : B.Apartment => n.val • x) '' Fa = Fa) :
    ∀ x ∈ Fa, n.val • x = x :=
  B.reflectionNormalizer_facet_fixing_of_AS4
    (B.affineRoot_mem_or_two_smul_mem_of_oppositePairs hF) hΨ hFa n hfix

/-- The facet conclusion also holds for actual normalizer elements in the
reflection subgroup enlarged by the action kernel. -/
theorem normalizer_facet_fixing_of_mem_reflectionNormalizer_sup_ker
    (hΨ : AffineRootSystem.IsLocallyFiniteReflectionArrangement B.affineRoots)
    {Fa : Set B.Apartment} (hFa : AffineRootSystem.IsFacet B.affineRoots Fa)
    (n : normalizerPoints B.i)
    (hn : n ∈ B.reflectionNormalizer ⊔ B.apartment.normalizerAffineEquiv.ker)
    (hfix : (fun x : B.Apartment => n • x) '' Fa = Fa) :
    ∀ x ∈ Fa, n • x = x := by
  have hw : B.apartment.normalizerAffineEquiv n ∈
      AffineRootSystem.affineWeylGroup B.affineRoots := by
    change n ∈ (AffineRootSystem.affineWeylGroup B.affineRoots).comap
      B.apartment.normalizerAffineEquiv
    rw [B.comap_affineWeylGroup_eq_reflectionNormalizer_sup_ker_of_oppositePairs hF hΨ]
    exact hn
  exact AffineRootSystem.affineWeyl_facet_fixing hΨ hFa
    ⟨B.apartment.normalizerAffineEquiv n, hw⟩ hfix

end Langlands.Geometry.Building.ValuationBuildingData
