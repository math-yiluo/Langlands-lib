import Langlands.Geometry.Building.ApartmentRootReflections
import Langlands.Geometry.Building.RootReflectionProof
import Langlands.Geometry.Building.RootReflectionWeyl
import Langlands.GroupScheme.Rational.RootFactorizationFromExistence
import Langlands.Geometry.Building.SimplyConnectedNormalizerAffineWeylStatement

/-! # The affine Weyl image from existence of actual opposite pairs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)

/-- Existence of opposite pairs suffices to realize all affine Weyl generators.
Uniqueness and the nonmultipliable-root clauses of rank-one factorization are
not required. -/
theorem affineWeylGroup_le_reflectionNormalizer_map_of_exists_oppositePairs
    (hA : B.SatisfiesApartmentAxioms)
    (hF : RelativeRoot.HasOppositeFactorPairs B.i) :
    AffineRootSystem.affineWeylGroup B.affineRoots ≤
      B.reflectionNormalizer.map B.apartment.normalizerAffineEquiv := by
  refine (Subgroup.closure_le _).2 ?_
  rintro e ⟨ψ, hψ, v, hv, rfl⟩
  have hψ' := B.apartment.affineRoots_subset_extendedAffineRoots hψ
  rw [← B.reflectionAffineRoots_eq] at hψ'
  obtain ⟨a, g, hg, hg1, rfl⟩ := hψ'
  obtain ⟨p, hp⟩ := hF a a.property g hg hg1
  refine ⟨B.reflectionElement hp,
    B.reflectionElement_mem_reflectionNormalizer hg hg1 hp, ?_⟩
  exact B.normalizerAffineEquiv_reflectionElement_eq_of_isCoroot_of_hasRootReflections
    hA (RootReflectionProof.hasRootReflections B) hg hg1 hp hv

/-- Under existence of opposite pairs, the actual root-reflection subgroup has
exactly the affine Weyl image. -/
theorem reflectionNormalizer_map_eq_affineWeylGroup_of_exists_oppositePairs
    (hA : B.SatisfiesApartmentAxioms)
    (hF : RelativeRoot.HasOppositeFactorPairs B.i) :
    B.reflectionNormalizer.map B.apartment.normalizerAffineEquiv =
      AffineRootSystem.affineWeylGroup B.affineRoots :=
  le_antisymm (B.reflectionNormalizer_map_le_affineWeylGroup_of_apartment hA)
    (B.affineWeylGroup_le_reflectionNormalizer_map_of_exists_oppositePairs hA hF)

end ValuationBuildingData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- Every affine Weyl element has an actual representative in the normalizer
intersection with the supplied simply connected image, provided actual opposite
pairs exist. -/
theorem affineWeylGroup_le_simplyConnectedNormalizer_map_of_exists_oppositePairs
    (hA : P.SatisfiesApartmentAxioms)
    (hF : RelativeRoot.HasOppositeFactorPairs P.i) :
    AffineRootSystem.affineWeylGroup P.affineRoots ≤
      (P.simplyConnectedImage.subgroupOf (normalizerPoints P.i)).map
        P.apartment.normalizerAffineEquiv :=
  (P.affineWeylGroup_le_reflectionNormalizer_map_of_exists_oppositePairs hA hF).trans
    (Subgroup.map_mono (P.reflectionNormalizer_le_simplyConnectedImage hA))

/-- A chosen actual normalizer representative in the supplied simply connected
image of an affine Weyl element. The choice uses only the apartment axioms and
existence of actual opposite factor pairs. -/
def affineWeylRepresentative
    (hA : P.SatisfiesApartmentAxioms)
    (hF : RelativeRoot.HasOppositeFactorPairs P.i)
    (w : AffineRootSystem.affineWeylGroup P.affineRoots) :
    P.simplyConnectedImage.subgroupOf (normalizerPoints P.i) :=
  ⟨Classical.choose
      (P.affineWeylGroup_le_simplyConnectedNormalizer_map_of_exists_oppositePairs
        hA hF w.property),
    (Classical.choose_spec
      (P.affineWeylGroup_le_simplyConnectedNormalizer_map_of_exists_oppositePairs
        hA hF w.property)).1⟩

/-- The chosen normalizer representative acts as the specified affine Weyl
element. -/
theorem normalizerAffineEquiv_affineWeylRepresentative
    (hA : P.SatisfiesApartmentAxioms)
    (hF : RelativeRoot.HasOppositeFactorPairs P.i)
    (w : AffineRootSystem.affineWeylGroup P.affineRoots) :
    P.apartment.normalizerAffineEquiv (P.affineWeylRepresentative hA hF w) = w :=
  (Classical.choose_spec
    (P.affineWeylGroup_le_simplyConnectedNormalizer_map_of_exists_oppositePairs
      hA hF w.property)).2

/-- Once opposite pairs exist, the desired image equality is equivalent to an
algebraic containment: every simply connected normalizer element is generated
by the actual root-reflection representatives and the kernel of the apartment
action. This leaves the upper inclusion explicit. -/
theorem simplyConnectedNormalizer_map_eq_affineWeylGroup_iff_le_reflections_sup_ker
    (hA : P.SatisfiesApartmentAxioms)
    (hF : RelativeRoot.HasOppositeFactorPairs P.i) :
    (P.simplyConnectedImage.subgroupOf (normalizerPoints P.i)).map
        P.apartment.normalizerAffineEquiv =
      AffineRootSystem.affineWeylGroup P.affineRoots ↔
    P.simplyConnectedImage.subgroupOf (normalizerPoints P.i) ≤
      P.reflectionNormalizer ⊔ P.apartment.normalizerAffineEquiv.ker := by
  rw [← P.reflectionNormalizer_map_eq_affineWeylGroup_of_exists_oppositePairs hA hF,
    le_antisymm_iff]
  have hle :
      P.reflectionNormalizer.map P.apartment.normalizerAffineEquiv ≤
        (P.simplyConnectedImage.subgroupOf (normalizerPoints P.i)).map
          P.apartment.normalizerAffineEquiv :=
    Subgroup.map_mono (P.reflectionNormalizer_le_simplyConnectedImage hA)
  exact (and_iff_left hle).trans Subgroup.map_le_map_iff

end ParahoricBuildingData

/-- The existing arbitrary-field rank-one target supplies the lower inclusion
for every datum in the exact normalizer-image target. -/
theorem affineWeylGroup_le_simplyConnectedNormalizer_map_of_rankOneStatement
    (hF : RootRankOneFactorizationStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)
    (hA : P.apartment.SatisfiesApartmentAxioms P.centralizer) :
    AffineRootSystem.affineWeylGroup P.affineRoots ≤
      (P.simplyConnectedImage.subgroupOf (normalizerPoints P.i)).map
        P.apartment.normalizerAffineEquiv :=
  P.affineWeylGroup_le_simplyConnectedNormalizer_map_of_apartment hA
    (hF F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus)

end Langlands.Geometry.Building
