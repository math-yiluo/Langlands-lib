import Langlands.Automorphic.GroupSchemeAdelicUniformGrowth
import Langlands.Automorphic.GroupSchemeTensorSmooth
import Langlands.Geometry.Manifold.VectorFieldCommutator

/-! # Actual enveloping differentiation preserving the algebraic-tensor condition -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints Langlands.Geometry.Manifold

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local instance actualDifferentialFiniteSmoothAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F G) :=
  Module.addCommMonoidToAddCommGroup ℂ

/-- The published manifold theorem proves the exact commutator for the original actual atlas. -/
theorem adelicDifferentialCommutator_of_smooth :
    AdelicDifferentialCommutator F G hsmooth := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  exact smoothVectorFieldCommutator_proof

/-- The original actual enveloping action, with its scalar-calculus premise discharged. -/
def actualAdelicEnvelopingAction :
    AdelicEnvelopingAlgebra F G hsmooth →ₐ[ℂ]
      Module.End ℂ (FinitePlotSmoothRationalFunctions F G) :=
  adelicEnvelopingAction F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)

/-- Proof irrelevance identifies this action with every earlier conditional realization. -/
theorem actualAdelicEnvelopingAction_eq (hcalc : AdelicDifferentialCommutator F G hsmooth) :
    actualAdelicEnvelopingAction F G hsmooth = adelicEnvelopingAction F G hsmooth hcalc := rfl

/-- The corresponding actual infinite-factor action uses the same calculus proof and atlas. -/
def actualInfiniteAdelicEnvelopingAction :
    AdelicEnvelopingAlgebra F G hsmooth →ₐ[ℂ]
      Module.End ℂ (InfinitePlotSmoothFunctions F G) :=
  plotSmoothEnvelopingAction F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)

/-- Every original finite slice intertwines the actual enveloping actions. -/
theorem finitePlotSmoothSlice_actualEnvelopingAction
    (a : AdelicEnvelopingAlgebra F G hsmooth) (b : FiniteAdelicGroupPoints F G)
    (f : FinitePlotSmoothRationalFunctions F G) :
    finitePlotSmoothSlice F G b (actualAdelicEnvelopingAction F G hsmooth a f) =
      actualInfiniteAdelicEnvelopingAction F G hsmooth a (finitePlotSmoothSlice F G b f) :=
  finitePlotSmoothSlice_envelopingAction F G hsmooth
    (adelicDifferentialCommutator_of_smooth F G hsmooth) a b f

/-- Smooth slices of a source tensor, bundled as a linear map. -/
def adelicSmoothTensorSlice (b : FiniteAdelicGroupPoints F G) :
    InfinitePlotSmoothFunctions F G ⊗[ℂ] FiniteLocallyConstantFunctions F G →ₗ[ℂ]
      InfinitePlotSmoothFunctions F G where
  toFun t := ⟨fun x => adelicSmoothTensorEvaluation F G t (AdelicGroupPoints.pair F G x b),
    adelicSmoothTensorEvaluation_infiniteSlice F G t b⟩
  map_add' t s := by
    apply Subtype.ext
    funext x
    exact congrFun ((adelicSmoothTensorEvaluation F G).map_add t s)
      (AdelicGroupPoints.pair F G x b)
  map_smul' z t := by
    apply Subtype.ext
    funext x
    exact congrFun ((adelicSmoothTensorEvaluation F G).map_smul z t)
      (AdelicGroupPoints.pair F G x b)

@[simp]
theorem adelicSmoothTensorSlice_tmul (b : FiniteAdelicGroupPoints F G)
    (a : InfinitePlotSmoothFunctions F G) (c : FiniteLocallyConstantFunctions F G) :
    adelicSmoothTensorSlice F G b (a ⊗ₜ[ℂ] c) = c b • a := by
  apply Subtype.ext
  funext x
  change adelicSmoothTensorEvaluation F G (a ⊗ₜ[ℂ] c) (AdelicGroupPoints.pair F G x b) =
    c b * a.val x
  simp only [adelicSmoothTensorEvaluation_tmul, AdelicGroupPoints.infinite_pair,
    AdelicGroupPoints.finite_pair, mul_comm]

/-- Applying any infinite-factor linear operator to the tensor retains a global finite tensor. -/
theorem adelicSmoothTensorSlice_map_left
    (D : Module.End ℂ (InfinitePlotSmoothFunctions F G))
    (t : InfinitePlotSmoothFunctions F G ⊗[ℂ] FiniteLocallyConstantFunctions F G)
    (b : FiniteAdelicGroupPoints F G) :
    adelicSmoothTensorSlice F G b (TensorProduct.map D LinearMap.id t) =
      D (adelicSmoothTensorSlice F G b t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a c => simp only [TensorProduct.map_tmul, LinearMap.id_apply,
      adelicSmoothTensorSlice_tmul, map_smul]
  | add t s ht hs => simp only [map_add, ht, hs]

/-- Actual enveloping differentiation preserves literal source tensor membership. -/
theorem actualAdelicEnvelopingAction_mem_tensorSmooth
    (a : AdelicEnvelopingAlgebra F G hsmooth) (f : FinitePlotSmoothRationalFunctions F G)
    (hf : f.val ∈ tensorSmoothSubrepresentation F G) :
    (actualAdelicEnvelopingAction F G hsmooth a f).val ∈ tensorSmoothSubrepresentation F G := by
  obtain ⟨t, ht⟩ := hf
  refine ⟨TensorProduct.map (actualInfiniteAdelicEnvelopingAction F G hsmooth a) LinearMap.id t, ?_⟩
  funext x
  let b := AdelicGroupPoints.finite F G x
  have hs : adelicSmoothTensorSlice F G b t = finitePlotSmoothSlice F G b f := by
    apply Subtype.ext
    funext y
    exact congrFun ht (AdelicGroupPoints.pair F G y b)
  have h := adelicSmoothTensorSlice_map_left F G
    (actualInfiniteAdelicEnvelopingAction F G hsmooth a) t b
  rw [hs, ← finitePlotSmoothSlice_actualEnvelopingAction F G hsmooth a b f] at h
  have hx := congrArg (fun s : InfinitePlotSmoothFunctions F G =>
    s.val (AdelicGroupPoints.infinite F G x)) h
  change adelicSmoothTensorEvaluation F G
      (TensorProduct.map (actualInfiniteAdelicEnvelopingAction F G hsmooth a) LinearMap.id t)
      (AdelicGroupPoints.pair F G (AdelicGroupPoints.infinite F G x) b) =
    evaluate F G (actualAdelicEnvelopingAction F G hsmooth a f).val
      (AdelicGroupPoints.pair F G (AdelicGroupPoints.infinite F G x) b) at hx
  change adelicSmoothTensorEvaluation F G
      (TensorProduct.map (actualInfiniteAdelicEnvelopingAction F G hsmooth a) LinearMap.id t) x =
    evaluate F G (actualAdelicEnvelopingAction F G hsmooth a f).val x
  simpa only [b, AdelicGroupPoints.pair_projections] using hx

/-- The tensor condition as an actual submodule of the original finite-smooth carrier. -/
def tensorFinitePlotSmoothSubmodule : Submodule ℂ (FinitePlotSmoothRationalFunctions F G) :=
  (tensorSmoothSubrepresentation F G).toSubmodule.comap
    (finitePlotSmoothRationalSubrepresentation F G).toSubmodule.subtype

/-- Restrict the actual original enveloping action to source tensor-smooth functions. -/
def tensorFinitePlotSmoothEnvelopingAction :
    AdelicEnvelopingAlgebra F G hsmooth →ₐ[ℂ]
      Module.End ℂ (tensorFinitePlotSmoothSubmodule F G) where
  toFun a :=
    { toFun := fun f => ⟨actualAdelicEnvelopingAction F G hsmooth a f.val,
        actualAdelicEnvelopingAction_mem_tensorSmooth F G hsmooth a f.val f.property⟩
      map_add' f g := Subtype.ext (map_add _ _ _)
      map_smul' z f := Subtype.ext (map_smul _ _ _) }
  map_zero' := by ext f; simp only [map_zero, LinearMap.zero_apply]; rfl
  map_one' := by ext f; simp only [map_one, Module.End.one_apply]; rfl
  map_add' := by intros; ext f; simp only [map_add, LinearMap.add_apply]; rfl
  map_mul' := by intros; ext f; simp only [map_mul, Module.End.mul_apply]; rfl
  commutes' := by intro z; ext f; simp only [AlgHom.commutes, Module.algebraMap_end_apply]; rfl

@[simp]
theorem tensorFinitePlotSmoothEnvelopingAction_val
    (a : AdelicEnvelopingAlgebra F G hsmooth) (f : tensorFinitePlotSmoothSubmodule F G) :
    (tensorFinitePlotSmoothEnvelopingAction F G hsmooth a f).val =
      actualAdelicEnvelopingAction F G hsmooth a f.val := rfl

end Langlands.Automorphic.GroupSchemeFunctions
