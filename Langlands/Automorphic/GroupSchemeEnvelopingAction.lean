import Langlands.Algebra.ComplexLieExtension
import Langlands.Automorphic.GroupSchemeFiniteLieDifferential

/-! # Conditional actual tangent enveloping actions on original adelic carriers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands

open Global Global.InfiniteAdelicGroupPoints Geometry.Manifold
open Automorphic.GroupSchemeFunctions

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] {d : ℕ}

namespace Global.InfiniteAdelicGroupPoints

/-- Complexification of the original actual identity-tangent Lie action. -/
def complexPlotSmoothLieAction (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) →
    (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))) →ₗ⁅ℂ⁆ Module.End ℂ (InfinitePlotSmoothFunctions F G) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  intro hcalc
  exact Algebra.ComplexLieExtension.lie (realPlotSmoothLieAction F G hsmooth hcalc)

@[simp]
theorem complexPlotSmoothLieAction_tmul (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
    (z : ℂ) (X : GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)),
    complexPlotSmoothLieAction F G hsmooth hcalc (z ⊗ₜ[ℝ] X) =
      z • plotSmoothDifferential F G hsmooth X := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  intros
  rfl

/-- Universal enveloping extension on the unchanged original smooth carrier. -/
def plotSmoothEnvelopingAction (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) →
    (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)))) →ₐ[ℂ] Module.End ℂ (InfinitePlotSmoothFunctions F G) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  intro hcalc
  exact Algebra.ComplexLieExtension.enveloping (realPlotSmoothLieAction F G hsmooth hcalc)

@[simp]
theorem plotSmoothEnvelopingAction_generator (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) (Z : ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))),
    plotSmoothEnvelopingAction F G hsmooth hcalc
        (UniversalEnvelopingAlgebra.ι ℂ Z) =
      complexPlotSmoothLieAction F G hsmooth hcalc Z := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  intro hcalc Z
  exact Algebra.ComplexLieExtension.enveloping_generator _ _

@[simp]
theorem plotSmoothEnvelopingAction_real_generator (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) (X : GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)),
    plotSmoothEnvelopingAction F G hsmooth hcalc
        (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) =
      plotSmoothDifferential F G hsmooth X := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  intro hcalc X
  exact Algebra.ComplexLieExtension.enveloping_real_generator _ _

/-- Restriction to the actual associative center of the actual enveloping algebra. -/
def plotSmoothCenterAction (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) →
    ↥(Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))))) →ₐ[ℂ] Module.End ℂ (InfinitePlotSmoothFunctions F G) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  intro hcalc
  exact (plotSmoothEnvelopingAction F G hsmooth hcalc).comp
    (Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))))).val

end Global.InfiniteAdelicGroupPoints

namespace Automorphic.GroupSchemeFunctions

/-- Complexification of the original actual identity-tangent Lie action. -/
def complexFinitePlotSmoothLieAction (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) →
    (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))) →ₗ⁅ℂ⁆ Module.End ℂ (FinitePlotSmoothRationalFunctions F G) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  intro hcalc
  exact Algebra.ComplexLieExtension.lie (realFinitePlotSmoothLieAction F G hsmooth hcalc)

@[simp]
theorem complexFinitePlotSmoothLieAction_tmul (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
    (z : ℂ) (X : GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)),
    complexFinitePlotSmoothLieAction F G hsmooth hcalc (z ⊗ₜ[ℝ] X) =
      z • finitePlotSmoothDifferentialAction F G hsmooth X := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  let : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  intros
  rfl

/-- Universal enveloping extension on the unchanged original smooth carrier. -/
def finitePlotSmoothEnvelopingAction (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) →
    (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)))) →ₐ[ℂ] Module.End ℂ (FinitePlotSmoothRationalFunctions F G) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  intro hcalc
  exact Algebra.ComplexLieExtension.enveloping (realFinitePlotSmoothLieAction F G hsmooth hcalc)

@[simp]
theorem finitePlotSmoothEnvelopingAction_generator (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) (Z : ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))),
    finitePlotSmoothEnvelopingAction F G hsmooth hcalc
        (UniversalEnvelopingAlgebra.ι ℂ Z) =
      complexFinitePlotSmoothLieAction F G hsmooth hcalc Z := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  let : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  intro hcalc Z
  exact Algebra.ComplexLieExtension.enveloping_generator _ _

@[simp]
theorem finitePlotSmoothEnvelopingAction_real_generator (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) (X : GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)),
    finitePlotSmoothEnvelopingAction F G hsmooth hcalc
        (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) =
      finitePlotSmoothDifferentialAction F G hsmooth X := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  let : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  intro hcalc X
  exact Algebra.ComplexLieExtension.enveloping_real_generator _ _

/-- Restriction to the actual associative center of the actual enveloping algebra. -/
def finitePlotSmoothCenterAction (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) →
    ↥(Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))))) →ₐ[ℂ] Module.End ℂ (FinitePlotSmoothRationalFunctions F G) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  intro hcalc
  exact (finitePlotSmoothEnvelopingAction F G hsmooth hcalc).comp
    (Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))))).val

/-- Original finite slices intertwine the actual complex tangent actions. -/
theorem finitePlotSmoothSlice_complexLieAction (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
    (Z : ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))) (b : FiniteAdelicGroupPoints F G)
    (f : FinitePlotSmoothRationalFunctions F G),
    finitePlotSmoothSlice F G b (complexFinitePlotSmoothLieAction F G hsmooth hcalc Z f) =
      complexPlotSmoothLieAction F G hsmooth hcalc Z (finitePlotSmoothSlice F G b f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  let : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  intro hcalc Z b
  induction Z using TensorProduct.inductionOn with
  | tmul z X =>
    intro f
    simp only [complexFinitePlotSmoothLieAction_tmul, complexPlotSmoothLieAction_tmul,
      LinearMap.smul_apply, map_smul, finitePlotSmoothSlice_differentialAction]
  | add U V hU hV =>
    intro f
    simp only [map_add, LinearMap.add_apply, hU, hV]

/-- The full actual enveloping actions intertwine under every original finite slice. -/
@[simp]
theorem finitePlotSmoothSlice_envelopingAction (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
    (u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)))) (b : FiniteAdelicGroupPoints F G)
    (f : FinitePlotSmoothRationalFunctions F G),
    finitePlotSmoothSlice F G b (finitePlotSmoothEnvelopingAction F G hsmooth hcalc u f) =
      plotSmoothEnvelopingAction F G hsmooth hcalc u (finitePlotSmoothSlice F G b f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  let : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  intro hcalc u b
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)))) u
  change ∀ f, finitePlotSmoothSlice F G b
      (finitePlotSmoothEnvelopingAction F G hsmooth hcalc
        (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t) f) =
    plotSmoothEnvelopingAction F G hsmooth hcalc
      (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t) (finitePlotSmoothSlice F G b f)
  induction t using TensorAlgebra.induction with
  | algebraMap z =>
    intro f
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, map_smul]
  | «ι» Z =>
    change ∀ f, finitePlotSmoothSlice F G b
        (finitePlotSmoothEnvelopingAction F G hsmooth hcalc
          (UniversalEnvelopingAlgebra.ι ℂ Z) f) =
      plotSmoothEnvelopingAction F G hsmooth hcalc
        (UniversalEnvelopingAlgebra.ι ℂ Z) (finitePlotSmoothSlice F G b f)
    simp only [finitePlotSmoothEnvelopingAction_generator, plotSmoothEnvelopingAction_generator]
    exact finitePlotSmoothSlice_complexLieAction F G hsmooth hcalc Z b
  | mul x y hx hy =>
    intro f
    simp only [map_mul, Module.End.mul_apply]
    rw [hx, hy]
  | add x y hx hy =>
    intro f
    simp only [map_add, LinearMap.add_apply, hx, hy]

/-- Finite right translation commutes with every actual enveloping differential. -/
theorem finitePlotSmoothEnvelopingAction_finiteRightAction (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
    (u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)))) (c : FiniteAdelicGroupPoints F G)
    (f : FinitePlotSmoothRationalFunctions F G),
    finitePlotSmoothEnvelopingAction F G hsmooth hcalc u
        (finitePlotSmoothRightAction F G (AdelicGroupPoints.ofFinite F G c) f) =
      finitePlotSmoothRightAction F G (AdelicGroupPoints.ofFinite F G c)
        (finitePlotSmoothEnvelopingAction F G hsmooth hcalc u f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  let : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  intro hcalc u c f
  apply finitePlotSmoothSlice_injective F G
  funext b
  dsimp only
  rw [finitePlotSmoothSlice_envelopingAction, finitePlotSmoothSlice_finiteRightAction,
    finitePlotSmoothSlice_finiteRightAction, finitePlotSmoothSlice_envelopingAction]

/-- Every specified finite subgroup fixing the input fixes every enveloping derivative. -/
theorem finitePlotSmoothEnvelopingAction_preserves_level (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
    (u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)))) (L : Subgroup (FiniteAdelicGroupPoints F G))
    (f : FinitePlotSmoothRationalFunctions F G),
    f.val ∈ levelSubmodule F G L →
      (finitePlotSmoothEnvelopingAction F G hsmooth hcalc u f).val ∈ levelSubmodule F G L := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  let : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  intro hcalc u L f hf l
  have hfix : finitePlotSmoothRightAction F G (AdelicGroupPoints.ofFinite F G l.val) f = f :=
    Subtype.ext (hf l)
  have h := congrArg (fun s : FinitePlotSmoothRationalFunctions F G => s.val)
    (finitePlotSmoothEnvelopingAction_finiteRightAction F G hsmooth hcalc u l.val f)
  rw [hfix] at h
  exact h.symm

/-- Compact finite level is retained with the same subgroup. -/
theorem finitePlotSmoothEnvelopingAction_hasFiniteLevel (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
    (u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)))) (f : FinitePlotSmoothRationalFunctions F G),
    HasFiniteLevel F G f.val →
      HasFiniteLevel F G (finitePlotSmoothEnvelopingAction F G hsmooth hcalc u f).val := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  let : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  intro hcalc u f hf
  obtain ⟨L, ho, hc, hL⟩ := hf
  exact ⟨L, ho, hc, finitePlotSmoothEnvelopingAction_preserves_level F G hsmooth hcalc u L f hL⟩

/-- The actual center actions also intertwine under every original finite slice. -/
@[simp]
theorem finitePlotSmoothSlice_centerAction (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  letI : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)))))
    (b : FiniteAdelicGroupPoints F G) (f : FinitePlotSmoothRationalFunctions F G),
    finitePlotSmoothSlice F G b (finitePlotSmoothCenterAction F G hsmooth hcalc z f) =
      plotSmoothCenterAction F G hsmooth hcalc z (finitePlotSmoothSlice F G b f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  let : AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
    Module.addCommMonoidToAddCommGroup ℂ
  intro hcalc z b f
  exact finitePlotSmoothSlice_envelopingAction F G hsmooth hcalc z.val b f

end Automorphic.GroupSchemeFunctions

end Langlands
