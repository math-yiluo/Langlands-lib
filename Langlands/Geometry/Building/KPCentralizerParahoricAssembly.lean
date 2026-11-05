import Langlands.Geometry.Building.KPMinimalLeviZeroStatement
import Langlands.Geometry.Building.KPSimplyConnectedImageNormal
import Langlands.Geometry.Building.KPSharpCoverImageStatement
import Langlands.Geometry.Building.SharpFixerBoundednessStatement
import Langlands.Geometry.Building.CentralizerParahoricReduction

/-! # Conditional assembly of the actual centralizer-parahoric intersection -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

namespace ZeroSubgroupDatum

variable {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {j : Z ⟶ G} (E : ZeroSubgroupDatum i j)

/-- The actual product description makes the cover-image containment sufficient
for the full zero-subgroup intersection comparison. -/
theorem centralizerZeroIntersection_of_coverImage
    (h : E.CoverImageCentralizerNormKernelStatement) :
    E.CentralizerZeroIntersectionStatement := by
  change E.zeroSubgroup.comap (rationalPoints.map j) ⊓
    Plancherel.rationalCommonNormKernel Z = E.centralizerZero
  apply le_antisymm _ E.centralizerZero_le_zeroSubgroup_comap_inf_normKernel
  rintro z ⟨hzG, hzNorm⟩
  obtain ⟨c, hc, z₀, hz₀, heq⟩ := E.mem_zeroSubgroup_iff.mp hzG
  have hdiff : rationalPoints.map j (z * z₀⁻¹) = c := by
    rw [map_mul, map_inv, ← heq, mul_inv_cancel_right]
  have hcover : z * z₀⁻¹ ∈ E.simplyConnectedImage.comap (rationalPoints.map j) := by
    change rationalPoints.map j (z * z₀⁻¹) ∈ E.simplyConnectedImage
    rw [hdiff]
    exact hc
  have hnorm : z * z₀⁻¹ ∈ Plancherel.rationalCommonNormKernel Z :=
    (Plancherel.rationalCommonNormKernel Z).mul_mem hzNorm
      ((Plancherel.rationalCommonNormKernel Z).inv_mem
        (E.centralizerZero_le_rationalCommonNormKernel hz₀))
  have hzero := h ⟨hcover, hnorm⟩
  simpa only [inv_mul_cancel_right] using E.centralizerZero.mul_mem hzero hz₀

/-- The smaller cover-image comparison and the full intersection comparison
are equivalent for every supplied actual zero datum. -/
theorem coverImageCentralizerNormKernel_iff_intersection :
    E.CoverImageCentralizerNormKernelStatement ↔ E.CentralizerZeroIntersectionStatement :=
  ⟨E.centralizerZeroIntersection_of_coverImage,
    E.coverImageCentralizerNormKernel_of_intersection⟩

end ZeroSubgroupDatum

namespace ParahoricBuildingData

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The three separate mathematical inputs suffice for the exact unchanged
centralizer-parahoric target. This statement does not assert those inputs. -/
def CentralizerParahoricAssemblyStatement : Prop :=
  P.zeroDatum.RootGroupLeSimplyConnectedImageStatement →
    P.toValuationBuildingData.SharpFixerBoundednessStatement →
    P.zeroDatum.CoverImageCentralizerNormKernelStatement →
    P.CentralizerParahoricIntersectionStatement

/-- Conditional assembly via the actual singleton sharp-centralizer inclusion. -/
theorem centralizerParahoricAssembly : P.CentralizerParahoricAssemblyStatement := by
  intro hroot hbound hcover
  apply P.centralizerParahoricReduction.mpr
  intro hax x g hg
  have hgZ := hg.1
  rw [← torusCentralizer_carrier_base, ← P.centralizer.isRepresentedBy.2] at hgZ
  obtain ⟨z, rfl⟩ := hgZ
  refine ⟨z, ?_, rfl⟩
  apply hcover
  exact ⟨P.sharpFixer_le_simplyConnectedImage_of_rootGroups hroot {x} hg.2,
    P.toValuationBuildingData.comap_sharpFixer_le_centralizerNormKernel
      hbound hax x hg.2⟩

/-- The published minimal-Levi comparisons supply the cover-image input to
the same conditional assembly. -/
theorem centralizerParahoricIntersection_of_minimalLeviComparison
    (hroot : P.zeroDatum.RootGroupLeSimplyConnectedImageStatement)
    (hbound : P.toValuationBuildingData.SharpFixerBoundednessStatement)
    (hzero : P.zeroDatum.MinimalLeviZeroComparisonStatement) :
    P.CentralizerParahoricIntersectionStatement :=
  P.centralizerParahoricAssembly hroot hbound
    (P.zeroDatum.coverImageCentralizerNormKernel_of_intersection hzero.2)

end ParahoricBuildingData

end Langlands.Geometry.Building
