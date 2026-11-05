import Langlands.Algebra.LieEnvelopingEquiv
import Langlands.Global.GeneralLinearInfiniteAdelicDifferential
import Langlands.Global.ArchimedeanDifferentialFaithful
import Langlands.Automorphic.GroupSchemeEnvelopingAction
import Langlands.Global.ArchimedeanEnvelopingAction

/-! # The actual general-linear tangent Lie and enveloping comparisons -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.GeneralLinearGroupPoints

open InfiniteAdelicGroupPoints Langlands.Geometry.Manifold
open Langlands.Automorphic.GroupSchemeFunctions

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GLG" =>
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance envelopingGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

variable {d : ℕ}

/-- Faithfulness of the original differential detects bracket preservation by
its actual identity-tangent comparison. The generic scalar commutator remains explicit. -/
theorem infiniteRealLieAlgebraEquiv_lie
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F GLG hsmooth
    letI := smoothLieGroup F GLG hsmooth
    letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
    ∀ (_hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d)
        (InfiniteAdelicGroupPoints F GLG))
      (X Y : GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG)),
      infiniteRealLieAlgebraEquiv F n hsmooth ⁅X, Y⁆ =
        ⁅infiniteRealLieAlgebraEquiv F n hsmooth X,
          infiniteRealLieAlgebraEquiv F n hsmooth Y⁆ := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  let := smoothLieGroup F GLG hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  intro hcalc X Y
  apply ArchimedeanGL.realSmoothDifferential_injective F n
  change ArchimedeanGL.smoothDifferential F n
      (infiniteRealLieAlgebraEquiv F n hsmooth ⁅X, Y⁆) =
    ArchimedeanGL.smoothDifferential F n
      ⁅infiniteRealLieAlgebraEquiv F n hsmooth X,
        infiniteRealLieAlgebraEquiv F n hsmooth Y⁆
  rw [ArchimedeanGL.smoothDifferential_commutator F n]
  apply LinearMap.ext
  intro f
  obtain ⟨f, rfl⟩ := (plotSmoothGeneralLinearEquiv F n).surjective f
  have h := congrArg
    (fun T : Module.End ℂ (InfinitePlotSmoothFunctions F GLG) =>
      plotSmoothGeneralLinearEquiv F n (T f))
    ((realPlotSmoothLieAction F GLG hsmooth hcalc).map_lie X Y)
  change plotSmoothGeneralLinearEquiv F n (plotSmoothDifferential F GLG hsmooth ⁅X, Y⁆ f) =
    plotSmoothGeneralLinearEquiv F n
      (plotSmoothDifferential F GLG hsmooth X (plotSmoothDifferential F GLG hsmooth Y f) -
        plotSmoothDifferential F GLG hsmooth Y (plotSmoothDifferential F GLG hsmooth X f)) at h
  simpa only [map_sub, plotSmoothGeneralLinearEquiv_differential,
    Module.End.mul_apply, LinearMap.sub_apply, LinearMap.comp_apply] using h

/-- Bundle the derivative of the original actual-point diffeomorphism as a Lie equivalence. -/
def infiniteRealLieEquiv
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F GLG hsmooth
    letI := smoothLieGroup F GLG hsmooth
    letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
    smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG) →
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG) ≃ₗ⁅ℝ⁆
        ArchimedeanGL.RealLieAlgebra F n := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  intro hcalc
  exact { infiniteRealLieAlgebraEquiv F n hsmooth with
    map_lie' := by
      intro X Y
      exact infiniteRealLieAlgebraEquiv_lie F n hsmooth hcalc X Y }


@[simp]
theorem infiniteRealLieEquiv_apply (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG)) (X : GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG)),
    infiniteRealLieEquiv F n hsmooth hcalc X = infiniteRealLieAlgebraEquiv F n hsmooth X := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  let := smoothLieGroup F GLG hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  intros
  rfl

/-- The actual complexified tangent Lie algebra is the original complex matrix Lie algebra. -/
def infiniteComplexLieEquiv (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG) →
    (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG))) ≃ₗ⁅ℂ⁆ ArchimedeanGL.ComplexLieAlgebra F n := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  intro hcalc
  exact Langlands.Algebra.LieEnvelopingEquiv.complex (infiniteRealLieEquiv F n hsmooth hcalc)

@[simp]
theorem infiniteComplexLieEquiv_tmul (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG)) (z : ℂ) (X : GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG)),
    infiniteComplexLieEquiv F n hsmooth hcalc (z ⊗ₜ[ℝ] X) =
      z ⊗ₜ[ℝ] infiniteRealLieAlgebraEquiv F n hsmooth X := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  let := smoothLieGroup F GLG hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  intros
  rfl

/-- The actual tangent universal enveloping algebra is the original matrix enveloping algebra. -/
def infiniteEnvelopingEquiv (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG) →
    (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG)))) ≃ₐ[ℂ] ArchimedeanGL.EnvelopingAlgebra F n := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  intro hcalc
  exact Langlands.Algebra.LieEnvelopingEquiv.enveloping
    (infiniteComplexLieEquiv F n hsmooth hcalc)

@[simp]
theorem infiniteEnvelopingEquiv_generator (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG)) (Z : ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG))),
    infiniteEnvelopingEquiv F n hsmooth hcalc (UniversalEnvelopingAlgebra.ι ℂ Z) =
      ArchimedeanGL.envelopingGenerator F n (infiniteComplexLieEquiv F n hsmooth hcalc Z) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  let := smoothLieGroup F GLG hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  intro hcalc Z
  exact Langlands.Algebra.LieEnvelopingEquiv.enveloping_generator _ _

/-- The comparison restricts to the actual associative enveloping centers. -/
def infiniteCenterEquiv (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG) →
    Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG)))) ≃ₐ[ℂ] ArchimedeanGL.EnvelopingCenter F n := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  intro hcalc
  exact Langlands.Algebra.LieEnvelopingEquiv.center (infiniteEnvelopingEquiv F n hsmooth hcalc)

@[simp]
theorem infiniteCenterEquiv_val (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG)) (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG))))),
    (infiniteCenterEquiv F n hsmooth hcalc z).val =
      infiniteEnvelopingEquiv F n hsmooth hcalc z.val := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  let := smoothLieGroup F GLG hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  intros
  rfl

/-- The original smooth-function equivalence intertwines the full complex Lie actions. -/
theorem plotSmoothGeneralLinearEquiv_complexLieAction (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG)) (Z : ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG))) (f : InfinitePlotSmoothFunctions F GLG),
    plotSmoothGeneralLinearEquiv F n (complexPlotSmoothLieAction F GLG hsmooth hcalc Z f) =
      ArchimedeanGL.complexSmoothLieAction F n (infiniteComplexLieEquiv F n hsmooth hcalc Z)
        (plotSmoothGeneralLinearEquiv F n f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  let := smoothLieGroup F GLG hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  intro hcalc Z f
  induction Z using TensorProduct.inductionOn with
  | tmul z X =>
    simp only [complexPlotSmoothLieAction_tmul, infiniteComplexLieEquiv_tmul,
      ArchimedeanGL.complexSmoothLieAction_tmul, LinearMap.smul_apply, map_smul,
      plotSmoothGeneralLinearEquiv_differential]
  | add U V hU hV =>
    simp only [map_add, LinearMap.add_apply, hU, hV]

/-- Conjugation by the original function equivalence identifies the actual algebra actions. -/
theorem plotSmoothGeneralLinearEquiv_conjEnvelopingAction (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG)),
    ((plotSmoothGeneralLinearEquiv F n).conjAlgEquiv ℂ).toAlgHom.comp
        (plotSmoothEnvelopingAction F GLG hsmooth hcalc) =
      (ArchimedeanGL.envelopingAction F n).comp
        (infiniteEnvelopingEquiv F n hsmooth hcalc).toAlgHom := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  let := smoothLieGroup F GLG hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  intro hcalc
  refine UniversalEnvelopingAlgebra.hom_ext ℂ
    (A := Module.End ℂ (ArchimedeanGL.SmoothFunctions F n))
    (L := ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG)))
    (g₁ := ((plotSmoothGeneralLinearEquiv F n).conjAlgEquiv ℂ).toAlgHom.comp
      (plotSmoothEnvelopingAction F GLG hsmooth hcalc))
    (g₂ := (ArchimedeanGL.envelopingAction F n).comp
      (infiniteEnvelopingEquiv F n hsmooth hcalc).toAlgHom) ?_
  apply LieHom.ext
  intro Z
  apply LinearMap.ext
  intro f
  change (plotSmoothGeneralLinearEquiv F n)
      (plotSmoothEnvelopingAction F GLG hsmooth hcalc (UniversalEnvelopingAlgebra.ι ℂ Z)
        ((plotSmoothGeneralLinearEquiv F n).symm f)) =
    ArchimedeanGL.envelopingAction F n
      (infiniteEnvelopingEquiv F n hsmooth hcalc (UniversalEnvelopingAlgebra.ι ℂ Z)) f
  rw [plotSmoothEnvelopingAction_generator, infiniteEnvelopingEquiv_generator,
    ArchimedeanGL.envelopingAction_generator,
    plotSmoothGeneralLinearEquiv_complexLieAction, LinearEquiv.apply_symm_apply]

/-- Every actual tangent enveloping differential becomes the original matrix differential. -/
theorem plotSmoothGeneralLinearEquiv_envelopingAction (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG)) (u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG)))) (f : InfinitePlotSmoothFunctions F GLG),
    plotSmoothGeneralLinearEquiv F n (plotSmoothEnvelopingAction F GLG hsmooth hcalc u f) =
      ArchimedeanGL.envelopingAction F n (infiniteEnvelopingEquiv F n hsmooth hcalc u)
        (plotSmoothGeneralLinearEquiv F n f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  let := smoothLieGroup F GLG hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  intro hcalc u f
  have h := congrArg (fun a => a u)
    (plotSmoothGeneralLinearEquiv_conjEnvelopingAction F n hsmooth hcalc)
  have he := LinearMap.congr_fun h (plotSmoothGeneralLinearEquiv F n f)
  change plotSmoothGeneralLinearEquiv F n
      (plotSmoothEnvelopingAction F GLG hsmooth hcalc u
        ((plotSmoothGeneralLinearEquiv F n).symm (plotSmoothGeneralLinearEquiv F n f))) = _ at he
  simpa only [LinearEquiv.symm_apply_apply, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom] using he

/-- The same original function comparison intertwines the actual center actions. -/
theorem plotSmoothGeneralLinearEquiv_centerAction (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F GLG hsmooth
  letI := smoothLieGroup F GLG hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  ∀ (hcalc : smoothVectorFieldCommutator 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG)) (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F GLG)))))
    (f : InfinitePlotSmoothFunctions F GLG),
    plotSmoothGeneralLinearEquiv F n (plotSmoothCenterAction F GLG hsmooth hcalc z f) =
      ArchimedeanGL.centerAction F n (infiniteCenterEquiv F n hsmooth hcalc z)
        (plotSmoothGeneralLinearEquiv F n f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  let := smoothLieGroup F GLG hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  intro hcalc z f
  exact plotSmoothGeneralLinearEquiv_envelopingAction F n hsmooth hcalc z.val f

end Langlands.Global.GeneralLinearGroupPoints
