import Langlands.Geometry.Building.CentralizerZeroSCNormalizerConjugation
import Langlands.Geometry.Building.KPSimplyConnectedImageNormal

/-! # Centralizer-zero conjugation by the zero-component normalizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- The actual zero-component normalizer has a product decomposition with its
first factor still in the normalizer and in the simply connected image. -/
theorem mem_normalizerZeroComponent_iff_exists_product (n : normalizerPoints P.i) :
    n ∈ P.normalizerZeroComponent ↔
      ∃ c : normalizerPoints P.i, (c : rationalPoints G) ∈ P.simplyConnectedImage ∧
        ∃ z ∈ P.centralizerZero, c * P.centralizer.toNormalizer z = n := by
  constructor
  · intro hn
    obtain ⟨c, hc, z, hz, heq⟩ :=
      P.zeroDatum.mem_zeroSubgroup_iff.mp hn
    change c * rationalPoints.map P.centralizer.j z = (n : rationalPoints G) at heq
    let cn : normalizerPoints P.i := n * (P.centralizer.toNormalizer z)⁻¹
    have hcn : (cn : rationalPoints G) = c := by
      change (n : rationalPoints G) * (rationalPoints.map P.centralizer.j z)⁻¹ = c
      rw [← heq]
      group
    refine ⟨cn, hcn ▸ hc, z, hz, ?_⟩
    dsimp [cn]
    group
  · rintro ⟨c, hc, z, hz, rfl⟩
    exact P.zeroDatum.zeroSubgroup.mul_mem
      (P.zeroDatum.simplyConnectedImage_le_zeroSubgroup hc)
      (P.zeroDatum.map_centralizerZero_le_zeroSubgroup ⟨z, hz, rfl⟩)

/-- Under the cover comparison, every actual point of `N(F) ∩ G(F)^0`
normalizes the full mapped centralizer-zero subgroup. -/
theorem mem_normalizer_map_centralizerZero_of_mem_normalizerZeroComponent
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (n : normalizerPoints P.i) (hn : n ∈ P.normalizerZeroComponent) :
    (n : rationalPoints G) ∈ Subgroup.normalizer
      (P.centralizerZero.map (rationalPoints.map P.centralizer.j) :
        Set (rationalPoints G)) := by
  obtain ⟨c, hc, z, hz, rfl⟩ :=
    (P.mem_normalizerZeroComponent_iff_exists_product n).mp hn
  exact (Subgroup.normalizer
    (P.centralizerZero.map (rationalPoints.map P.centralizer.j) :
      Set (rationalPoints G))).mul_mem
        (P.mem_normalizer_map_centralizerZero_of_mem_simplyConnectedImage hZ c hc)
        (Subgroup.le_normalizer ⟨z, hz, rfl⟩)

/-- Conjugation by such a point preserves membership in the original mapped
centralizer-zero subgroup. -/
theorem conj_mem_map_centralizerZero_of_mem_normalizerZeroComponent
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (n : normalizerPoints P.i) (hn : n ∈ P.normalizerZeroComponent)
    {g : rationalPoints G}
    (hg : g ∈ P.centralizerZero.map (rationalPoints.map P.centralizer.j)) :
    (n : rationalPoints G) * g * (n : rationalPoints G)⁻¹ ∈
      P.centralizerZero.map (rationalPoints.map P.centralizer.j) :=
  (Subgroup.mem_normalizer_iff.mp
    (P.mem_normalizer_map_centralizerZero_of_mem_normalizerZeroComponent hZ n hn) g).mp hg

/-- The zero-component normalizer normalizes `normalizerZero` inside the actual
normalizer group. -/
theorem normalizerZeroComponent_le_normalizer_normalizerZero
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement) :
    P.normalizerZeroComponent ≤ Subgroup.normalizer
      (P.normalizerZero : Set (normalizerPoints P.i)) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro g
  rw [P.mem_normalizerZero_iff, P.mem_normalizerZero_iff]
  exact Subgroup.mem_normalizer_iff.mp
    (P.mem_normalizer_map_centralizerZero_of_mem_normalizerZeroComponent hZ n hn) g

/-- The actual centralizer-zero subgroup is normal in `N(F) ∩ G(F)^0`.
Normality in the full normalizer is a separate assertion. -/
theorem normalizerZero_subgroupOf_normalizerZeroComponent_normal
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement) :
    (P.normalizerZero.subgroupOf P.normalizerZeroComponent).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    P.normalizerZero_le_normalizerZeroComponent).mpr
      (P.normalizerZeroComponent_le_normalizer_normalizerZero hZ)

/-- Literal ambient conjugation restricted to the full mapped centralizer-zero
subgroup for an actual zero-component normalizer point. -/
def centralizerZeroComponentNormalizerAut
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (n : normalizerPoints P.i) (hn : n ∈ P.normalizerZeroComponent) :
    MulAut (P.centralizerZero.map (rationalPoints.map P.centralizer.j)) :=
  ((MulAut.conj (n : rationalPoints G)).subgroupMap
    (P.centralizerZero.map (rationalPoints.map P.centralizer.j))).trans
      (MulEquiv.subgroupCongr
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (P.mem_normalizer_map_centralizerZero_of_mem_normalizerZeroComponent hZ n hn)))

@[simp]
theorem coe_centralizerZeroComponentNormalizerAut
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (n : normalizerPoints P.i) (hn : n ∈ P.normalizerZeroComponent)
    (g : P.centralizerZero.map (rationalPoints.map P.centralizer.j)) :
    (P.centralizerZeroComponentNormalizerAut hZ n hn g : rationalPoints G) =
      (n : rationalPoints G) * g * (n : rationalPoints G)⁻¹ :=
  rfl

end Langlands.Geometry.Building.ParahoricBuildingData
