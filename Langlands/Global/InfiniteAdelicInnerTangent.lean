import Langlands.Global.InfiniteAdelicTangentKernelNaturality
import Langlands.GroupScheme.Lie.InnerAdjoint

/-! # Tangent conjugation by rational points of `G(F_∞)` and the adjoint action -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Opposite
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.GroupScheme Langlands.Geometry.Manifold

variable (F : Type u) [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

/-- Conjugation by the image in `G(F_∞)` of a point over the base is the point map of the inner
automorphism; so its tangent map at the identity is the tangent map of that automorphism. -/
theorem groupTangentConjugation_constantPoint (n : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    groupTangentConjugation 𝓘(ℝ, smoothModel F d)
        (G.constantPoint n ((algSpec (CommRingCat.of F)).obj
          (op (CommAlgCat.of F (InfiniteAdeleRing F))))) =
      pointTangent F hsmooth hsmooth (G.innerIso n).hom := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  have h : (G.affinePointsTarget (G.innerIso n).hom (CommAlgCat.of F (InfiniteAdeleRing F)) :
      InfiniteAdelicGroupPoints F G → InfiniteAdelicGroupPoints F G) =
      fun x => G.constantPoint n ((algSpec (CommRingCat.of F)).obj
          (op (CommAlgCat.of F (InfiniteAdeleRing F)))) * x *
        (G.constantPoint n ((algSpec (CommRingCat.of F)).obj
          (op (CommAlgCat.of F (InfiniteAdeleRing F)))))⁻¹ := by
    funext x
    rw [affinePointsTarget_apply]
    exact G.comp_innerIso_hom n _ x
  change mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, smoothModel F d)
      (fun x => G.constantPoint n ((algSpec (CommRingCat.of F)).obj
          (op (CommAlgCat.of F (InfiniteAdeleRing F)))) * x *
        (G.constantPoint n ((algSpec (CommRingCat.of F)).obj
          (op (CommAlgCat.of F (InfiniteAdeleRing F)))))⁻¹) 1 =
    mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, smoothModel F d)
      (G.affinePointsTarget (G.innerIso n).hom (CommAlgCat.of F (InfiniteAdeleRing F))) 1
  rw [h]

/-- The Lie vector of the tangent conjugate of `X` by a base point is the adjoint image of the
Lie vector of `X`. -/
theorem tangentKernel_groupTangentConjugation [IsAffineHom G.X.hom]
    (n : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (X : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    Additive.ofMul (tangentKernel F hsmooth (groupTangentConjugation 𝓘(ℝ, smoothModel F d)
        (G.constantPoint n ((algSpec (CommRingCat.of F)).obj
          (op (CommAlgCat.of F (InfiniteAdeleRing F))))) X)) =
      adjoint G (InfiniteAdeleRing F) (G.constantPoint n _)
        (Additive.ofMul (tangentKernel F hsmooth X)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  rw [groupTangentConjugation_constantPoint F hsmooth n, ← Lie.targetMapLinear_innerIso]
  apply Additive.toMul.injective
  apply Subtype.ext
  exact tangentPoint_pointTangent F hsmooth hsmooth (G.innerIso n).hom X

end Langlands.Global.InfiniteAdelicGroupPoints
