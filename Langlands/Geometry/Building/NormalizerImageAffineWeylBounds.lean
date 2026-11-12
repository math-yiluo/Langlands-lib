import Langlands.Geometry.Building.ReflectionNormalizerWeylAction
import Langlands.Geometry.Building.SimplyConnectedFacetFixingReduction
import Langlands.Geometry.Building.KPApartmentAxioms

/-!
# The first sentence of AS 5 from AS 3, AS 4 and V 6

For valuation building data `B` of a connected reductive group over a nonarchimedean local field
(which includes V 6 on all of `Z(F)`), the first sentence of KP Axiom 4.1.6, AS 5, follows from
AS 3 and AS 4: the image of `N(F)` in the affine automorphisms of the apartment contains `W(Ψ)`
and is contained in `W(Ψ)ᵉˣᵗ`.

The lower bound is `affineWeylGroup_le_normalizerAffineEquiv_range_of_isAffineRootSystem`. For
the upper bound, every `n ∈ N(F)` is a product `r z` of a product `r` of opposite-pair
reflections and a point `z ∈ Z(F)` (`exists_reflection_mul_centralizer`, using that reflection
products realize every relative Weyl class). By AS 4, `r` acts through `W(Ψ) ≤ W(Ψ)ᵉˣᵗ`; by V 6,
`z` acts by a translation, which preserves `Ψ` and has trivial derivative.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)

/-- A point of `Z(F)` acts on the apartment through `W(Ψ)ᵉˣᵗ`: it preserves the affine roots, and
by V 6 it acts by a translation, whose derivative is trivial. -/
theorem normalizerAffineEquiv_centralizer_mem_extendedAffineWeylGroup
    (z : rationalPoints B.centralizer.Z) :
    B.apartment.normalizerAffineEquiv (B.centralizer.toNormalizer z) ∈
      AffineRootSystem.extendedAffineWeylGroup B.affineRoots := by
  refine AffineRootSystem.mem_extendedAffineWeylGroup.2
    ⟨B.apartment.normalizerAffineEquiv_mem_rootStabilizer _, ?_⟩
  rw [B.isOmegaCompatible.normalizerAffineEquiv_eq z]
  exact one_mem _

/-- Under AS 4, the image of `N(F)` is contained in `W(Ψ)ᵉˣᵗ`. -/
theorem range_le_extendedAffineWeylGroup_of_AS4
    (h4 : ∀ ψ ∈ B.apartment.extendedAffineRoots,
      ψ ∈ B.affineRoots ∨ (2 : ℝ) • ψ ∈ B.affineRoots) :
    B.apartment.normalizerAffineEquiv.range ≤
      AffineRootSystem.extendedAffineWeylGroup B.affineRoots := by
  rintro _ ⟨n, rfl⟩
  obtain ⟨r, hr, z, rfl⟩ :=
    B.exists_reflection_mul_centralizer B.reflectionRelativeWeylMap_surjective' n
  rw [map_mul]
  exact mul_mem
    (AffineRootSystem.affineWeylGroup_le_extendedAffineWeylGroup _
      (B.reflectionNormalizer_map_le_affineWeylGroup_of_AS4 h4 ⟨r, hr, rfl⟩))
    (B.normalizerAffineEquiv_centralizer_mem_extendedAffineWeylGroup z)

/-- Under AS 3, the image of `N(F)` contains `W(Ψ)`. -/
theorem affineWeylGroup_le_range_of_AS3
    (hΨ : AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots) :
    AffineRootSystem.affineWeylGroup B.affineRoots ≤ B.apartment.normalizerAffineEquiv.range :=
  B.affineWeylGroup_le_normalizerAffineEquiv_range_of_isAffineRootSystem hΨ
    B.hasOppositeFactorPairs

end Langlands.Geometry.Building.ValuationBuildingData
