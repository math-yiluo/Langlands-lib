import Langlands.Geometry.Building.KPZeroNormKernel

/-! # Zero subgroups of actual minimal Levi subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ZeroSubgroupDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {j : Z ⟶ G} (E : ZeroSubgroupDatum i j)

/-- The local-field consequence of KP Lemma 2.6.27: in a simply connected
ambient group, the actual minimal-Levi zero subgroup is its norm-one subgroup. -/
def CentralizerZeroNormKernelStatement : Prop :=
  IsSimplyConnected G →
    E.centralizerZero = Plancherel.rationalCommonNormKernel Z

/-- The second assertion of KP Corollary 2.6.28, using the supplied actual
zero datum and actual centralizer inclusion. -/
def CentralizerZeroIntersectionStatement : Prop :=
  E.zeroSubgroup.comap (rationalPoints.map j) ⊓
      Plancherel.rationalCommonNormKernel Z = E.centralizerZero

/-- The cover-image containment in the proof of KP Corollary 2.6.28,
restricted to base-field points. It is a consequence of the full intersection
comparison and is enough for a sharp subgroup known to lie in the cover image. -/
def CoverImageCentralizerNormKernelStatement : Prop :=
  E.simplyConnectedImage.comap (rationalPoints.map j) ⊓
      Plancherel.rationalCommonNormKernel Z ≤ E.centralizerZero

/-- The two local-field zero-subgroup comparisons needed from KP 2.6.27–2.6.28.
These are targets, not additional fields of `ZeroSubgroupDatum`. -/
def MinimalLeviZeroComparisonStatement : Prop :=
  E.CentralizerZeroNormKernelStatement ∧ E.CentralizerZeroIntersectionStatement

/-- The inclusion from the actual centralizer-zero subgroup into the
intersection is already available without the missing reverse comparison. -/
theorem centralizerZero_le_zeroSubgroup_comap_inf_normKernel :
    E.centralizerZero ≤ E.zeroSubgroup.comap (rationalPoints.map j) ⊓
      Plancherel.rationalCommonNormKernel Z := by
  intro z hz
  exact ⟨E.map_centralizerZero_le_zeroSubgroup ⟨z, hz, rfl⟩,
    E.centralizerZero_le_rationalCommonNormKernel hz⟩

/-- The full zero-subgroup comparison implies the cover-image containment. -/
theorem coverImageCentralizerNormKernel_of_intersection
    (h : E.CentralizerZeroIntersectionStatement) :
    E.CoverImageCentralizerNormKernelStatement := by
  change E.zeroSubgroup.comap (rationalPoints.map j) ⊓
    Plancherel.rationalCommonNormKernel Z = E.centralizerZero at h
  intro z hz
  rw [← h]
  exact ⟨E.simplyConnectedImage_le_zeroSubgroup hz.1, hz.2⟩

end Langlands.Geometry.Building.ZeroSubgroupDatum
