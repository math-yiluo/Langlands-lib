import Langlands.AlgebraicGeometry.ProjectiveBundle.TensorFrameOverlap

/-! # Tensor-line invariance of actual projective frame bundles -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Modules
open Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.RelativeProjectiveSpace

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveBundle.TensorFrames

variable {S : Scheme.{u}} {M N : S.Modules} {n : ℕ}
variable (hM : IsLocallyFreeOfRank M (n + 1)) (hN : IsLocallyFreeRankOne N)

lemma chartFunctor_map_eq {U V : (sourceAtlas hM hN).openCover.I₀} (h : U ⟶ V) :
    (tensorAtlas hM hN).cocycle.chartFunctor.map h =
      (sourceAtlas hM hN).cocycle.chartFunctor.map h := by
  change (U.property.1.some.tensor U.property.2.some).projectiveChange
      (V.property.1.some.tensor V.property.2.some) U.val le_rfl (leOfHom h) ≫
        RelativeProjectiveSpace.map n ((tensorAtlas hM hN).openCover.trans h) =
    U.property.1.some.projectiveChange V.property.1.some U.val le_rfl (leOfHom h) ≫
      RelativeProjectiveSpace.map n ((sourceAtlas hM hN).openCover.trans h)
  rw [LocalFrame.tensor_overlap_projectiveChange]
  rfl

/-- The source atlas is a Cartesian atlas for the tensor cocycle because their scheme
transition maps agree. -/
def sourceCartesianAtlas :
    (tensorAtlas hM hN).cocycle.CartesianAtlas (sourceAtlas hM hN).bundle
      (sourceAtlas hM hN).toBase where
  chart := (sourceAtlas hM hN).cocycle.chart
  compatible h := by
    rw [chartFunctor_map_eq]
    simpa only [CoordinateCocycle.chartFunctor, Category.assoc] using
      (sourceAtlas hM hN).cocycle.transition_chart h
  cartesian := (sourceAtlas hM hN).cocycle.isPullback_chart

/-- The actual glued schemes of the joint tensor and source atlases are isomorphic. -/
def atlasIso : (tensorAtlas hM hN).bundle ≅ (sourceAtlas hM hN).bundle :=
  (sourceCartesianAtlas hM hN).schemeIso

@[reassoc (attr := simp)]
lemma chart_atlasIso_hom (U : (sourceAtlas hM hN).opens) :
    (tensorAtlas hM hN).cocycle.chart U ≫ (atlasIso hM hN).hom =
      (sourceAtlas hM hN).cocycle.chart U :=
  (sourceCartesianAtlas hM hN).chart_schemeIso_hom U

@[reassoc (attr := simp)]
lemma atlasIso_hom_toBase :
    (atlasIso hM hN).hom ≫ (sourceAtlas hM hN).toBase =
      (tensorAtlas hM hN).toBase :=
  (sourceCartesianAtlas hM hN).schemeIso_hom_toBase

/-- Tensoring a locally free sheaf of positive fixed rank by a line bundle preserves
its actual projective frame bundle, over the original scheme. -/
def frameBundleIso :
    frameBundle (tensorObj M N) n (isLocallyFreeOfRank_tensor hM hN) ≅
      frameBundle M n hM :=
  ((tensorAtlas hM hN).toFrameBundleIso (isLocallyFreeOfRank_tensor hM hN)).symm ≪≫
    atlasIso hM hN ≪≫ (sourceAtlas hM hN).toFrameBundleIso hM

@[reassoc (attr := simp)]
lemma frameBundleIso_hom_toBase :
    (frameBundleIso hM hN).hom ≫ FrameBundle.toBase hM =
      FrameBundle.toBase (isLocallyFreeOfRank_tensor hM hN) := by
  simp [frameBundleIso]

@[reassoc (attr := simp)]
lemma frameBundleIso_inv_toBase :
    (frameBundleIso hM hN).inv ≫ FrameBundle.toBase (isLocallyFreeOfRank_tensor hM hN) =
      FrameBundle.toBase hM := by
  rw [← frameBundleIso_hom_toBase hM hN, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

end Langlands.AlgebraicGeometry.ProjectiveBundle.TensorFrames
