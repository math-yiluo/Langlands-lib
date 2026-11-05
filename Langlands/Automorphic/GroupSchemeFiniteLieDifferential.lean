import Langlands.Automorphic.GroupSchemeFiniteDifferential
import Langlands.Automorphic.GroupSchemeLieDifferential

/-! # Conditional Lie action on the original finite-smooth adelic carrier -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints
open Langlands.Geometry.Manifold

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] {d : ℕ}

/-- Faithful original slice extraction lifts the conditional actual Lie action
without changing its finite-smooth carrier or derivative. -/
def realFinitePlotSmoothLieAction (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
    letI : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
      Module.addCommMonoidToAddCommGroup ℂ
    smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) →
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) →ₗ⁅ℝ⁆
        Module.End ℂ (FinitePlotSmoothRationalFunctions F G) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  intro hcalc
  refine { realFinitePlotSmoothDifferential F G hsmooth with map_lie' := ?_ }
  intro X Y
  apply LinearMap.ext
  intro f
  apply finitePlotSmoothSlice_injective F G
  funext b
  change finitePlotSmoothSlice F G b
      (finitePlotSmoothDifferentialAction F G hsmooth
        (⁅X, Y⁆ :
          GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) f) =
    finitePlotSmoothSlice F G b
      (finitePlotSmoothDifferentialAction F G hsmooth X
          (finitePlotSmoothDifferentialAction F G hsmooth Y f) -
        finitePlotSmoothDifferentialAction F G hsmooth Y
          (finitePlotSmoothDifferentialAction F G hsmooth X f))
  simp only [map_sub, finitePlotSmoothSlice_differentialAction]
  exact congrArg (fun D => D (finitePlotSmoothSlice F G b f))
    ((realPlotSmoothLieAction F G hsmooth hcalc).map_lie X Y)

end Langlands.Automorphic.GroupSchemeFunctions
