import Langlands.Automorphic.GroupSchemeManifoldSmooth
import Langlands.Geometry.Manifold.SmoothGroupDifferential

/-! # Actual tangent differential on the original infinite adelic smooth space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.Geometry.Manifold

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] {d : ℕ}

/-- Actual differentiation, acting on the existing original plot-smooth carrier. -/
def plotSmoothDifferential (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) →
      Module.End ℂ (G.plotSmoothFunctions (CommAlgCat.of F (InfiniteAdeleRing F))
      (B := mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  intro X
  refine
    { toFun := fun f => ⟨groupDirectionalValue 𝓘(ℝ, smoothModel F d) X f.val, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · apply (isPlotSmooth_iff_contMDiff F G hsmooth _).mpr
    exact contMDiff_groupDirectionalValue _ X
      ((isPlotSmooth_iff_contMDiff F G hsmooth f.val).mp f.property)
  · intro f h
    apply Subtype.ext
    funext g
    exact groupDirectionalValue_add _ X
      ((isPlotSmooth_iff_contMDiff F G hsmooth f.val).mp f.property)
      ((isPlotSmooth_iff_contMDiff F G hsmooth h.val).mp h.property) g
  · intro c f
    apply Subtype.ext
    funext g
    exact groupDirectionalValue_const_smul _ X c
      ((isPlotSmooth_iff_contMDiff F G hsmooth f.val).mp f.property) g

@[simp]
theorem plotSmoothDifferential_apply
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (X : smoothModel F d) (f : (G.plotSmoothFunctions (CommAlgCat.of F (InfiniteAdeleRing F))
      (B := mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom)) (g : InfiniteAdelicGroupPoints F G) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F G hsmooth
    (plotSmoothDifferential F G hsmooth X f).val g =
      mvfderiv 𝓘(ℝ, smoothModel F d) (fun h => f.val (g * h)) 1 X := rfl

/-- The actual tangent direction depends real-linearly on the identity tangent. -/
def realPlotSmoothDifferential (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) →ₗ[ℝ]
      Module.End ℂ (G.plotSmoothFunctions (CommAlgCat.of F (InfiniteAdeleRing F))
      (B := mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  refine
    { toFun := plotSmoothDifferential F G hsmooth
      map_add' := ?_
      map_smul' := ?_ }
  · intro X Y
    ext f g
    exact groupDirectionalValue_add_direction _ X Y f.val g
  · intro c X
    ext f g
    exact groupDirectionalValue_smul_direction _ c X f.val g

/-- Pullback by actual left multiplication on the original smooth functions. -/
def plotSmoothLeftTranslation (a : InfiniteAdelicGroupPoints F G) : Module.End ℂ (G.plotSmoothFunctions (CommAlgCat.of F (InfiniteAdeleRing F))
      (B := mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom) where
  toFun f := ⟨fun x => f.val (a * x),
    GroupScheme.IsPlotSmooth.leftTranslate G _ _ f.property a⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem plotSmoothLeftTranslation_apply
    (a g : InfiniteAdelicGroupPoints F G) (f : (G.plotSmoothFunctions (CommAlgCat.of F (InfiniteAdeleRing F))
      (B := mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom)) :
    (plotSmoothLeftTranslation F G a f).val g = f.val (a * g) := rfl

/-- Differentiation commutes with the original actual left pullback. -/
theorem plotSmoothDifferential_leftTranslation
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (X : smoothModel F d) (a : InfiniteAdelicGroupPoints F G) (f : (G.plotSmoothFunctions (CommAlgCat.of F (InfiniteAdeleRing F))
      (B := mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom)) :
    plotSmoothDifferential F G hsmooth X (plotSmoothLeftTranslation F G a f) =
      plotSmoothLeftTranslation F G a (plotSmoothDifferential F G hsmooth X f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  apply Subtype.ext
  funext g
  exact groupDirectionalValue_leftTranslation _ X a f.val g

/-- Connected reductivity alone supplies the atlas and actual tangent action. -/
def reductiveRealPlotSmoothDifferential (hG : GroupScheme.IsConnectedReductive G) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := reductiveChartedSpace F G hG
    GroupLieAlgebra 𝓘(ℝ, smoothModel F hG.smoothDimension)
      (InfiniteAdelicGroupPoints F G) →ₗ[ℝ] Module.End ℂ (G.plotSmoothFunctions (CommAlgCat.of F (InfiniteAdeleRing F))
      (B := mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom) :=
  realPlotSmoothDifferential F G hG.smoothDimension_spec

end Langlands.Global.InfiniteAdelicGroupPoints
