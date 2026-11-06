import Langlands.Automorphic.GroupSchemeFiniteLevelSlices
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Topology.LocallyConstant.Algebra

/-! # The actual algebraic-tensor smooth adelic function image -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

/-- Positive right translation on all functions on the actual adelic group. -/
def adelicFunctionRightAction :
    Representation ℂ (AdelicGroupPoints F G) (AdelicGroupPoints F G → ℂ) where
  toFun g :=
    { toFun := fun f x => f (x * g)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by ext f x; exact congrArg f (mul_one x)
  map_mul' g h := by ext f x; exact congrArg f (mul_assoc x g h).symm

/-- Finite-place smooth functions here mean all locally constant functions,
with no common open right stabilizer imposed. -/
abbrev FiniteLocallyConstantFunctions :=
  LocallyConstant (FiniteAdelicGroupPoints F G) ℂ

/-- Positive finite right translation preserves local constancy. -/
def finiteLocallyConstantFunctionRightAction :
    Representation ℂ (FiniteAdelicGroupPoints F G) (FiniteLocallyConstantFunctions F G) where
  toFun g :=
    { toFun := fun f => ⟨fun x => f (x * g),
        f.isLocallyConstant.comp_continuous (continuous_id.mul continuous_const)⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by ext f x; exact congrArg f (mul_one x)
  map_mul' g h := by ext f x; exact congrArg f (mul_assoc x g h).symm

/-- The separated-variable bilinear map uses the actual infinite and finite projections. -/
def adelicSmoothSeparatedBilinear :
    InfinitePlotSmoothFunctions F G →ₗ[ℂ]
      FiniteLocallyConstantFunctions F G →ₗ[ℂ] (AdelicGroupPoints F G → ℂ) where
  toFun a :=
    { toFun := fun b x => a.val (AdelicGroupPoints.infinite F G x) *
        b (AdelicGroupPoints.finite F G x)
      map_add' b c := by ext x; exact mul_add _ _ _
      map_smul' c b := by
        ext x
        change _ * (c * _) = c * (_ * _)
        ring }
  map_add' a b := by ext c x; exact add_mul _ _ _
  map_smul' c a := by
    ext b x
    change (c * _) * _ = c * (_ * _)
    exact mul_assoc _ _ _

/-- Evaluation of the algebraic tensor product in actual functions. -/
def adelicSmoothTensorEvaluation :
    InfinitePlotSmoothFunctions F G ⊗[ℂ] FiniteLocallyConstantFunctions F G →ₗ[ℂ]
      (AdelicGroupPoints F G → ℂ) :=
  TensorProduct.lift (adelicSmoothSeparatedBilinear F G)

@[simp]
theorem adelicSmoothTensorEvaluation_tmul (a : InfinitePlotSmoothFunctions F G)
    (b : FiniteLocallyConstantFunctions F G) (x : AdelicGroupPoints F G) :
    adelicSmoothTensorEvaluation F G (a ⊗ₜ[ℂ] b) x =
      a.val (AdelicGroupPoints.infinite F G x) * b (AdelicGroupPoints.finite F G x) := rfl

/-- The actual function image of the algebraic tensor, not an unrestricted slice condition. -/
def adelicTensorSmoothFunctions : Submodule ℂ (AdelicGroupPoints F G → ℂ) :=
  LinearMap.range (adelicSmoothTensorEvaluation F G)

/-- Membership gives one finite decomposition valid at every adelic point. -/
theorem mem_adelicTensorSmoothFunctions_iff (f : AdelicGroupPoints F G → ℂ) :
    f ∈ adelicTensorSmoothFunctions F G ↔
      ∃ s : Finset (InfinitePlotSmoothFunctions F G × FiniteLocallyConstantFunctions F G),
        ∀ x : AdelicGroupPoints F G, f x = ∑ p ∈ s,
          p.1.val (AdelicGroupPoints.infinite F G x) *
            p.2 (AdelicGroupPoints.finite F G x) := by
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := TensorProduct.exists_finset t
    refine ⟨s, ?_⟩
    intro x
    rw [hs, map_sum]
    simp only [Finset.sum_apply, adelicSmoothTensorEvaluation_tmul]
  · rintro ⟨s, hs⟩
    refine ⟨∑ p ∈ s, p.1 ⊗ₜ[ℂ] p.2, ?_⟩
    ext x
    simpa only [map_sum, Finset.sum_apply, adelicSmoothTensorEvaluation_tmul] using (hs x).symm

/-- Translating the two factors gives an actual tensor representative of the translate. -/
def adelicSmoothTensorTranslate (g : AdelicGroupPoints F G) :
    Module.End ℂ (InfinitePlotSmoothFunctions F G ⊗[ℂ] FiniteLocallyConstantFunctions F G) :=
  TensorProduct.map
    (G.plotSmoothRightAction (CommAlgCat.of F (InfiniteAdeleRing F))
      (B := mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom
      (AdelicGroupPoints.infinite F G g))
    (finiteLocallyConstantFunctionRightAction F G (AdelicGroupPoints.finite F G g))

/-- The tensor construction intertwines the original positive full right translations. -/
theorem adelicSmoothTensorEvaluation_translate (g x : AdelicGroupPoints F G)
    (t : InfinitePlotSmoothFunctions F G ⊗[ℂ] FiniteLocallyConstantFunctions F G) :
    adelicSmoothTensorEvaluation F G (adelicSmoothTensorTranslate F G g t) x =
      adelicSmoothTensorEvaluation F G t (x * g) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    change a.val (AdelicGroupPoints.infinite F G x * AdelicGroupPoints.infinite F G g) *
        b (AdelicGroupPoints.finite F G x * AdelicGroupPoints.finite F G g) =
      a.val (AdelicGroupPoints.infinite F G (x * g)) *
        b (AdelicGroupPoints.finite F G (x * g))
    simp only [map_mul]
  | add t s ht hs => simpa only [map_add, Pi.add_apply] using congrArg₂ (· + ·) ht hs

/-- The algebraic-tensor image is stable under the actual full adelic right action. -/
def adelicTensorSmoothSubrepresentation :
    Subrepresentation (adelicFunctionRightAction F G) where
  toSubmodule := adelicTensorSmoothFunctions F G
  apply_mem_toSubmodule g f hf := by
    obtain ⟨t, rfl⟩ := hf
    refine ⟨adelicSmoothTensorTranslate F G g t, ?_⟩
    funext x
    exact adelicSmoothTensorEvaluation_translate F G g x t

/-- Infinite slices of an evaluated tensor are plot-smooth. -/
theorem adelicSmoothTensorEvaluation_infiniteSlice
    (t : InfinitePlotSmoothFunctions F G ⊗[ℂ] FiniteLocallyConstantFunctions F G)
    (b : FiniteAdelicGroupPoints F G) :
    (fun a : InfiniteAdelicGroupPoints F G =>
      adelicSmoothTensorEvaluation F G t (AdelicGroupPoints.pair F G a b)) ∈
        InfinitePlotSmoothFunctions F G := by
  induction t using TensorProduct.inductionOn with
  | tmul a c =>
    convert (InfinitePlotSmoothFunctions F G).smul_mem (c b) a.property using 1
    funext x
    change a.val (AdelicGroupPoints.infinite F G (AdelicGroupPoints.pair F G x b)) *
      c (AdelicGroupPoints.finite F G (AdelicGroupPoints.pair F G x b)) = c b * a.val x
    rw [AdelicGroupPoints.infinite_pair, AdelicGroupPoints.finite_pair, mul_comm]
  | add t s ht hs =>
    have heq : (fun a => adelicSmoothTensorEvaluation F G (t + s)
        (AdelicGroupPoints.pair F G a b)) =
        (fun a => adelicSmoothTensorEvaluation F G t (AdelicGroupPoints.pair F G a b)) +
        (fun a => adelicSmoothTensorEvaluation F G s (AdelicGroupPoints.pair F G a b)) := by
      funext a
      exact congrFun ((adelicSmoothTensorEvaluation F G).map_add t s)
        (AdelicGroupPoints.pair F G a b)
    rw [heq]
    exact (InfinitePlotSmoothFunctions F G).add_mem ht hs

/-- Finite slices of an evaluated tensor are locally constant, without a common stabilizer. -/
theorem adelicSmoothTensorEvaluation_finiteSlice
    (t : InfinitePlotSmoothFunctions F G ⊗[ℂ] FiniteLocallyConstantFunctions F G)
    (a : InfiniteAdelicGroupPoints F G) :
    IsLocallyConstant (fun b : FiniteAdelicGroupPoints F G =>
      adelicSmoothTensorEvaluation F G t (AdelicGroupPoints.pair F G a b)) := by
  induction t using TensorProduct.inductionOn with
  | tmul c b =>
    simpa only [adelicSmoothTensorEvaluation_tmul, AdelicGroupPoints.infinite_pair,
      AdelicGroupPoints.finite_pair, Function.comp_def, LocallyConstant.toFun_eq_coe] using
      b.isLocallyConstant.comp (fun z => c.val a * z)
  | add t s ht hs =>
    have heq : (fun b => adelicSmoothTensorEvaluation F G (t + s)
        (AdelicGroupPoints.pair F G a b)) =
        (fun b => adelicSmoothTensorEvaluation F G t (AdelicGroupPoints.pair F G a b)) +
        (fun b => adelicSmoothTensorEvaluation F G s (AdelicGroupPoints.pair F G a b)) := by
      funext b
      exact congrFun ((adelicSmoothTensorEvaluation F G).map_add t s)
        (AdelicGroupPoints.pair F G a b)
    rw [heq]
    exact ht.add hs

/-- Ordinary manifold smoothness of the infinite factors makes tensor evaluation continuous. -/
theorem continuous_adelicSmoothTensorEvaluation {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (t : InfinitePlotSmoothFunctions F G ⊗[ℂ] FiniteLocallyConstantFunctions F G) :
    Continuous (adelicSmoothTensorEvaluation F G t) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    exact ((((InfiniteAdelicGroupPoints.isPlotSmooth_iff_contMDiff F G hsmooth _).mp
      a.property).continuous).comp (AdelicGroupPoints.infinite F G).continuous).mul
        (b.continuous.comp (AdelicGroupPoints.finite F G).continuous)
  | add t s ht hs => simpa only [map_add] using ht.add hs

/-- Literal algebraic-tensor membership on the original continuous rational-invariant carrier. -/
def tensorSmoothSubrepresentation : Subrepresentation (continuousRightAction F G) where
  toSubmodule := (adelicTensorSmoothFunctions F G).comap
    ((RationalInvariantFunctions F G).subtype.comp (ContinuousRationalFunctions F G).subtype)
  apply_mem_toSubmodule g f hf := by
    exact (adelicTensorSmoothSubrepresentation F G).apply_mem_toSubmodule g hf

/-- Tensor membership implies the already existing smooth-slice conditions. -/
theorem tensorSmooth_le_plotSmooth :
    tensorSmoothSubrepresentation F G ≤ plotSmoothSubrepresentation F G := by
  intro f hf
  obtain ⟨t, ht⟩ := hf
  constructor
  · apply (mem_infinitePlotSmoothSubrepresentation F G f).mpr
    intro b
    change infiniteSlice F G b f ∈ InfinitePlotSmoothFunctions F G
    have heq : infiniteSlice F G b f =
        fun a => adelicSmoothTensorEvaluation F G t (AdelicGroupPoints.pair F G a b) := by
      funext a
      exact (congrFun ht (AdelicGroupPoints.pair F G a b)).symm
    rw [heq]
    exact adelicSmoothTensorEvaluation_infiniteSlice F G t b
  · intro a
    have heq : (fun b => evaluate F G f (AdelicGroupPoints.pair F G a b)) =
        fun b => adelicSmoothTensorEvaluation F G t (AdelicGroupPoints.pair F G a b) := by
      funext b
      exact (congrFun ht (AdelicGroupPoints.pair F G a b)).symm
    rw [heq]
    exact adelicSmoothTensorEvaluation_finiteSlice F G t a

/-- A uniform finite stabilizer is imposed separately from the source tensor condition. -/
def finiteTensorSmoothSubrepresentation : Subrepresentation (continuousRightAction F G) :=
  tensorSmoothSubrepresentation F G ⊓ finiteSmoothSubrepresentation F G

/-- The tensor-and-stabilizer space embeds into the previous broader finite-smooth carrier. -/
theorem finiteTensorSmooth_le_finitePlotSmooth :
    finiteTensorSmoothSubrepresentation F G ≤ finitePlotSmoothRationalSubrepresentation F G := by
  intro f hf
  exact ⟨(tensorSmooth_le_plotSmooth F G hf.1).1, hf.2⟩

/-- The exact inclusion retains the original functions and full right translations. -/
def finiteTensorSmoothInclusion :
    (finiteTensorSmoothSubrepresentation F G).toRepresentation.IntertwiningMap
      (finitePlotSmoothRightAction F G) where
  toLinearMap := (finiteTensorSmoothSubrepresentation F G).toSubmodule.inclusion
    (finiteTensorSmooth_le_finitePlotSmooth F G)
  isIntertwining' _ := by ext; rfl

end Langlands.Automorphic.GroupSchemeFunctions
