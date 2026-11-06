import Langlands.Automorphic.GroupSchemeActualDifferential
import Langlands.Automorphic.GroupSchemeForms
import Langlands.Automorphic.DifferentialInfiniteFiniteProof
import Langlands.Geometry.Manifold.SmoothGroupConjugation

/-! # Actual enveloping differentiation of whole adelic finite vectors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints Langlands.Geometry.Manifold

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local instance finiteVectorDifferentialAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

/-- Differentiate actual inner conjugation in the original smooth atlas. -/
def adelicTangentConjugation (g : InfiniteAdelicGroupPoints F G) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    smoothModel F d →L[ℝ] smoothModel F d := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  exact groupTangentConjugation 𝓘(ℝ, smoothModel F d) g

/-- The value of every original finite slice after positive infinite translation. -/
theorem finitePlotSmoothSlice_infiniteRightAction_apply
    (b : FiniteAdelicGroupPoints F G) (g x : InfiniteAdelicGroupPoints F G)
    (f : FinitePlotSmoothRationalFunctions F G) :
    (finitePlotSmoothSlice F G b
      (finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G g) f)).val x =
        (finitePlotSmoothSlice F G b f).val (x * g) := by
  change evaluate F G f.val
    (AdelicGroupPoints.pair F G x b * AdelicGroupPoints.ofInfinite F G g) = _
  rw [AdelicGroupPoints.ofInfinite_eq_pair, AdelicGroupPoints.pair_mul, mul_one]
  rfl

/-- Covariance holds for the original actual derivative and the whole adelic function. -/
theorem finitePlotSmoothDifferentialAction_infiniteRightAction
    (g : InfiniteAdelicGroupPoints F G) (X : smoothModel F d)
    (f : FinitePlotSmoothRationalFunctions F G) :
    finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G g)
        (finitePlotSmoothDifferentialAction F G hsmooth X f) =
      finitePlotSmoothDifferentialAction F G hsmooth (adelicTangentConjugation F G hsmooth g X)
        (finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G g) f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  apply finitePlotSmoothSlice_injective F G
  funext b
  dsimp only
  rw [finitePlotSmoothSlice_differentialAction]
  apply Subtype.ext
  funext x
  rw [finitePlotSmoothSlice_infiniteRightAction_apply,
    finitePlotSmoothSlice_differentialAction]
  have heq : (finitePlotSmoothSlice F G b
      (finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G g) f)).val =
      fun y => (finitePlotSmoothSlice F G b f).val (y * g) := by
    funext y
    exact finitePlotSmoothSlice_infiniteRightAction_apply F G b g y f
  change groupDirectionalValue 𝓘(ℝ, smoothModel F d) X
      (finitePlotSmoothSlice F G b f).val (x * g) =
    groupDirectionalValue 𝓘(ℝ, smoothModel F d) (adelicTangentConjugation F G hsmooth g X)
      (finitePlotSmoothSlice F G b
        (finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G g) f)).val x
  rw [heq]
  exact groupDirectionalValue_rightTranslation _ g X
    ((isPlotSmooth_iff_contMDiff F G hsmooth _).mp
      (finitePlotSmoothSlice F G b f).property) x

/-- The finite-dimensional complexified actual tangent acts on the unchanged carrier. -/
def actualAdelicComplexDifferential :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    (ℂ ⊗[ℝ] smoothModel F d) →ₗ[ℂ]
      Module.End ℂ (FinitePlotSmoothRationalFunctions F G) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  exact (complexFinitePlotSmoothLieAction F G hsmooth
    (adelicDifferentialCommutator_of_smooth F G hsmooth)).toLinearMap

@[simp]
theorem actualAdelicComplexDifferential_tmul :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    ∀ (z : ℂ) (X : smoothModel F d),
    actualAdelicComplexDifferential F G hsmooth (z ⊗ₜ[ℝ] X) =
      z • finitePlotSmoothDifferentialAction F G hsmooth X := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  dsimp only
  intro z X
  rfl

private theorem actualComplexTangent_finite :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    Module.Finite ℂ (ℂ ⊗[ℝ] smoothModel F d) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  infer_instance

/-- The full adelic function remains a finite vector after an actual real derivative. -/
theorem IsAdelicInfiniteFinite.realDifferential
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (X : smoothModel F d)
    {f : FinitePlotSmoothRationalFunctions F G} (hf : IsAdelicInfiniteFinite F G Kinf f) :
    IsAdelicInfiniteFinite F G Kinf (finitePlotSmoothDifferentialAction F G hsmooth X f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := actualComplexTangent_finite F (d := d)
  have h : Langlands.FiniteVectors.IsFiniteVector
      (finitePlotSmoothInfiniteSubgroupAction F G Kinf)
      (actualAdelicComplexDifferential F G hsmooth ((1 : ℂ) ⊗ₜ[ℝ] X) f) := by
    apply Langlands.FiniteVectors.isFiniteVector_bilinear_of_covariance
      (finitePlotSmoothInfiniteSubgroupAction F G Kinf)
      (actualAdelicComplexDifferential F G hsmooth) ((1 : ℂ) ⊗ₜ[ℝ] X) hf
    intro g
    refine ⟨(1 : ℂ) ⊗ₜ[ℝ] adelicTangentConjugation F G hsmooth g.val X, ?_⟩
    simp only [actualAdelicComplexDifferential_tmul, one_smul]
    change finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G g.val)
        (finitePlotSmoothDifferentialAction F G hsmooth X f) =
      finitePlotSmoothDifferentialAction F G hsmooth
        (adelicTangentConjugation F G hsmooth g.val X)
        (finitePlotSmoothRightAction F G (AdelicGroupPoints.ofInfinite F G g.val) f)
    exact finitePlotSmoothDifferentialAction_infiniteRightAction F G hsmooth g.val X f
  simpa only [IsAdelicInfiniteFinite, actualAdelicComplexDifferential_tmul, one_smul] using h

/-- Complexification preserves the same full-function orbit finiteness. -/
theorem IsAdelicInfiniteFinite.complexDifferential
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    ∀ (Z : ℂ ⊗[ℝ] smoothModel F d) {f : FinitePlotSmoothRationalFunctions F G},
      IsAdelicInfiniteFinite F G Kinf f →
        IsAdelicInfiniteFinite F G Kinf (actualAdelicComplexDifferential F G hsmooth Z f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  dsimp only
  intro Z f hf
  induction Z using TensorProduct.inductionOn with
  | tmul z X =>
    rw [actualAdelicComplexDifferential_tmul, LinearMap.smul_apply]
    exact (IsAdelicInfiniteFinite.realDifferential F G hsmooth Kinf X hf).smul z
  | add X Y hX hY =>
    simp only [map_add, LinearMap.add_apply]
    exact hX.add hY

/-- The actual enveloping generator is the original complex tangent differential. -/
theorem actualAdelicEnvelopingAction_generator :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F G hsmooth
    let := smoothLieGroup F G hsmooth
    let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
    ∀ Z : ℂ ⊗[ℝ] smoothModel F d,
      actualAdelicEnvelopingAction F G hsmooth (UniversalEnvelopingAlgebra.ι ℂ Z) =
        actualAdelicComplexDifferential F G hsmooth Z := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  dsimp only
  intro Z
  exact finitePlotSmoothEnvelopingAction_generator F G hsmooth
    (adelicDifferentialCommutator_of_smooth F G hsmooth) Z

/-- Every element of the actual enveloping algebra preserves whole adelic finite vectors. -/
theorem IsAdelicInfiniteFinite.envelopingAction
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    (a : AdelicEnvelopingAlgebra F G hsmooth)
    {f : FinitePlotSmoothRationalFunctions F G} (hf : IsAdelicInfiniteFinite F G Kinf f) :
    IsAdelicInfiniteFinite F G Kinf (actualAdelicEnvelopingAction F G hsmooth a f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ
      (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))) a
  change IsAdelicInfiniteFinite F G Kinf (actualAdelicEnvelopingAction F G hsmooth
    (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t) f)
  induction t using TensorAlgebra.induction generalizing f with
  | algebraMap z =>
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one,
      LinearMap.smul_apply, Module.End.one_apply]
    exact hf.smul z
  | «ι» Z =>
    change IsAdelicInfiniteFinite F G Kinf (actualAdelicEnvelopingAction F G hsmooth
      (UniversalEnvelopingAlgebra.ι ℂ Z) f)
    rw [actualAdelicEnvelopingAction_generator]
    exact IsAdelicInfiniteFinite.complexDifferential F G hsmooth Kinf Z hf
  | mul x y hx hy =>
    simp only [map_mul, Module.End.mul_apply]
    exact hx (hy hf)
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply]
    exact (hx hf).add (hy hf)

/-- Restrict the actual action to the original whole-function finite-vector submodule. -/
def adelicInfiniteFiniteEnvelopingAction
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) :
    AdelicEnvelopingAlgebra F G hsmooth →ₐ[ℂ]
      Module.End ℂ (adelicInfiniteFiniteSubmodule F G Kinf) where
  toFun a :=
    { toFun := fun f => ⟨actualAdelicEnvelopingAction F G hsmooth a f.val,
        IsAdelicInfiniteFinite.envelopingAction F G hsmooth Kinf a f.property⟩
      map_add' f g := Subtype.ext (map_add _ _ _)
      map_smul' z f := Subtype.ext (map_smul _ _ _) }
  map_zero' := by ext f; simp only [map_zero, LinearMap.zero_apply]; rfl
  map_one' := by ext f; simp only [map_one, Module.End.one_apply]; rfl
  map_add' := by intros; ext f; simp only [map_add, LinearMap.add_apply]; rfl
  map_mul' := by intros; ext f; simp only [map_mul, Module.End.mul_apply]; rfl
  commutes' := by intro z; ext f; simp only [AlgHom.commutes, Module.algebraMap_end_apply]; rfl

@[simp]
theorem adelicInfiniteFiniteEnvelopingAction_val
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    (a : AdelicEnvelopingAlgebra F G hsmooth) (f : adelicInfiniteFiniteSubmodule F G Kinf) :
    (adelicInfiniteFiniteEnvelopingAction F G hsmooth Kinf a f).val =
      actualAdelicEnvelopingAction F G hsmooth a f.val := rfl

end Langlands.Automorphic.GroupSchemeFunctions
