import Langlands.Global.InfiniteAdelicTangentKernel
import Langlands.Global.InfiniteAdelicLeviEnveloping

/-! # Naturality of the dual-number tangent points of `G(F_∞)` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable (F : Type u) [Field F] [NumberField F] {H G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [IsAffine G.X.left] {e d : ℕ}
  (hsmoothH : SmoothOfRelativeDimension e H.X.hom) (hsmooth : SmoothOfRelativeDimension d G.X.hom)

/-- The chain rule at a point given up to equality. -/
theorem mfderiv_comp_apply_of_eq {E E' E'' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    {M M' : Type*} [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace M']
    [ChartedSpace E' M'] {f : M → M'} {g : M' → E''} {x : M} {y : M'}
    (hg : MDifferentiableAt 𝓘(ℝ, E') 𝓘(ℝ, E'') g y) (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E') f x)
    (hy : f x = y) (w : TangentSpace 𝓘(ℝ, E) x) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E'') (g ∘ f) x w =
      mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E'') g y (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E') f x w) := by
  subst hy
  exact mfderiv_comp_apply _ hg hf w

/-- The derivative along the image of `X` under the tangent map of `j` is the derivative along
`X` of the pulled-back regular function (chain rule). -/
theorem regularDerivative_pointTangent (j : H ⟶ G)
    (X : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F H hsmoothH
      GroupLieAlgebra 𝓘(ℝ, smoothModel F e) (InfiniteAdelicGroupPoints F H))
    (a : AffineCoordinateRing F G.X) :
    regularDerivative F hsmooth (pointTangent F hsmoothH hsmooth j X) a =
      regularDerivative F hsmoothH X (j.hom.hom.left.appTop a) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F H hsmoothH
  let := smoothChartedSpace F G hsmooth
  funext v
  have hj := contMDiff_affinePointsTarget F hsmoothH hsmooth j
  have hf := contMDiff_placeValue F hsmooth v a
  have h1 : H.affinePointsTarget j (CommAlgCat.of F (InfiniteAdeleRing F)) 1 = 1 := map_one _
  exact (mfderiv_comp_apply_of_eq (hf.mdifferentiable (by simp) _)
    (hj.mdifferentiable (by simp) 1) h1 X).symm

/-- Naturality: the dual-number point of the image of `X` under the tangent map of `j` is the
image under `j` of the dual-number point of `X`. -/
theorem tangentPoint_pointTangent (j : H ⟶ G)
    (X : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F H hsmoothH
      GroupLieAlgebra 𝓘(ℝ, smoothModel F e) (InfiniteAdelicGroupPoints F H)) :
    tangentPoint F hsmooth (pointTangent F hsmoothH hsmooth j X) =
      tangentPoint F hsmoothH X ≫ j.hom.hom := by
  apply G.affinePointEvaluation_injective (CommAlgCat.of F (DualNumber (InfiniteAdeleRing F)))
  refine funext fun a : AffineCoordinateRing F G.X => ?_
  have h1 : H.affinePointsTarget j (CommAlgCat.of F (InfiniteAdeleRing F)) 1 = 1 := map_one _
  have hid : identityValue F (G := G) a = identityValue F (G := H) (j.hom.hom.left.appTop a) := by
    change G.affinePointEvaluation _ 1 a =
      G.affinePointEvaluation _ (H.affinePointsTarget j (CommAlgCat.of F (InfiniteAdeleRing F)) 1) a
    rw [h1]
  refine (affinePointEvaluation_tangentPoint F hsmooth _ a).trans ?_
  refine Eq.trans ?_ (affinePointEvaluation_tangentPoint F hsmoothH X
    (j.hom.hom.left.appTop a)).symm
  apply TrivSqZeroExt.ext
  · exact (tangentAlgHom_fst F hsmooth _ a).trans
      (hid.trans (tangentAlgHom_fst F hsmoothH X _).symm)
  · exact (tangentAlgHom_snd F hsmooth _ a).trans
      ((regularDerivative_pointTangent F hsmoothH hsmooth j X a).trans
        (tangentAlgHom_snd F hsmoothH X _).symm)

/-- `tangentKernel` carries the tangent map of `j` to the Lie map of `j`. -/
theorem tangentKernel_pointTangent (j : H ⟶ G)
    (X : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F H hsmoothH
      GroupLieAlgebra 𝓘(ℝ, smoothModel F e) (InfiniteAdelicGroupPoints F H)) :
    Additive.ofMul (tangentKernel F hsmooth (pointTangent F hsmoothH hsmooth j X)) =
      Lie.targetMapLinear j (InfiniteAdeleRing F) (Additive.ofMul (tangentKernel F hsmoothH X)) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact tangentPoint_pointTangent F hsmoothH hsmooth j X

end Langlands.Global.InfiniteAdelicGroupPoints
