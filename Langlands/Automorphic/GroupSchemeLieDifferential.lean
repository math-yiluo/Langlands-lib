import Langlands.Automorphic.GroupSchemeDifferential
import Langlands.Geometry.Manifold.SmoothGroupLieDifferential
import Mathlib.Algebra.Lie.OfAssociative

/-! # Conditional Lie bundling of the actual infinite adelic differential -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.Geometry.Manifold

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] {d : ℕ}

/-- The original actual tangent differential is a Lie homomorphism when the
explicit generic scalar-commutator prerequisite holds. -/
def realPlotSmoothLieAction (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
    smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) →
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) →ₗ⁅ℝ⁆
        Module.End ℂ (G.plotSmoothFunctions (CommAlgCat.of F (InfiniteAdeleRing F))
          (B := mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  intro hcalc
  refine { realPlotSmoothDifferential F G hsmooth with map_lie' := ?_ }
  intro X Y
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext g
  change groupDirectionalValue 𝓘(ℝ, smoothModel F d) ⁅X, Y⁆ f.val g =
    groupDirectionalValue 𝓘(ℝ, smoothModel F d) X
      (groupDirectionalValue 𝓘(ℝ, smoothModel F d) Y f.val) g -
        groupDirectionalValue 𝓘(ℝ, smoothModel F d) Y
          (groupDirectionalValue 𝓘(ℝ, smoothModel F d) X f.val) g
  exact groupDirectionalValue_commutator_of_vectorFieldCommutator _ hcalc X Y
    ((isPlotSmooth_iff_contMDiff F G hsmooth f.val).mp f.property) g

end Langlands.Global.InfiniteAdelicGroupPoints
