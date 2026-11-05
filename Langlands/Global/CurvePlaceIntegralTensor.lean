/-
The finite-coefficient and compact-image arguments adapt
`Langlands.Global.AdelicFunctoriality.IntegralLocalComparisonProof`
(Worker 461), which adapts Imperial FLT, commit
923d45174c500aa1d994ba973bac38ea39eacbf7,
FLT/DedekindDomain/Completion/BaseChange.lean:364-547,854-870.
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Andrew Yang, Matthew Jasper
The upstream license is retained at licenses/ImperialCollegeLondon-FLT/LICENSE.
Modified by Worker 208 (2026): use the actual curve-place integral closure,
original completed-integer embeddings, a shorter cancellation-of-base-change
transport, flatness for integral injectivity, and the proved full integral
lattice density rather than a separate Chinese-remainder argument. Retain
inseparable original extensions and rational-function presentations.
-/
import Langlands.Global.CurvePlaceIntegralLattice
import Langlands.Global.FunctionFieldAdelesLocallyCompactProof
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.Domain
import Mathlib.RingTheory.TensorProduct.Maps

/-! # The actual integral tensor comparison at a function-field place -/

noncomputable section

universe u

open IsDedekindDomain
open scoped TensorProduct Langlands.Global.CurvePlaceCompletionExtension
  Langlands.Global.CurvePlaceCompletedIntegersExtension
  Langlands.Global.CurvePlaceIntegralClosure Langlands.Global.CurvePlaceIntegralPrimes

namespace Langlands.Global.CurvePlaceIntegralTensor

variable {k K L : Type u} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L]
  (p : AlgebraicCurve.Place k K) (q : CurvePlacesAbove k L p)

scoped instance (priority := 50) :
    Algebra p.toValuationSubring (curvePlaceCompletionIntegers q.1) :=
  ((CurvePlaceCompletedIntegersExtension.completionIntegersMap p q).comp
    (curvePlaceIntegersMap p)).toAlgebra

scoped instance : IsScalarTower p.toValuationSubring
    (curvePlaceCompletionIntegers p) (curvePlaceCompletionIntegers q.1) :=
  .of_algebraMap_eq fun _ => rfl

/-- The original integral closure maps to the actual upper completed integer ring. -/
def originalIntegersMap :
    curvePlaceIntegralClosure L p →ₐ[p.toValuationSubring] curvePlaceCompletionIntegers q.1 :=
  { toRingHom := (curvePlaceIntegersMap q.1).comp
      (CurvePlaceIntegralPrimes.integersMap p q).toRingHom
    commutes' r := by
      change curvePlaceIntegersMap q.1 (CurvePlaceCompletionExtension.integersMap p q r) =
        CurvePlaceCompletedIntegersExtension.completionIntegersMap p q (curvePlaceIntegersMap p r)
      exact (CurvePlaceCompletedIntegersExtension.completionIntegersMap_original p q r).symm }

@[simp]
theorem originalIntegersMap_coe (b : curvePlaceIntegralClosure L p) :
    (originalIntegersMap p q b : curvePlaceCompletion q.1) =
      algebraMap L (curvePlaceCompletion q.1) (b : L) := rfl

scoped instance (priority := 50) :
    Algebra (curvePlaceIntegralClosure L p) (curvePlaceCompletionIntegers q.1) :=
  (originalIntegersMap p q).toRingHom.toAlgebra

scoped instance : IsScalarTower p.toValuationSubring
    (curvePlaceIntegralClosure L p) (curvePlaceCompletionIntegers q.1) :=
  .of_algebraMap_eq fun r => (originalIntegersMap p q).commutes r |>.symm

/-- The canonical actual integral tensor homomorphism to all upper integer rings. -/
def integralTensorMap :
    curvePlaceCompletionIntegers p ⊗[p.toValuationSubring] curvePlaceIntegralClosure L p →ₐ[
      curvePlaceCompletionIntegers p]
      (∀ q : CurvePlacesAbove k L p, curvePlaceCompletionIntegers q.1) :=
  AlgHom.pi fun q => Algebra.TensorProduct.lift
    (Algebra.ofId _ _) (originalIntegersMap p q) (fun _ _ => .all _ _)

@[simp]
theorem integralTensorMap_tmul (a : curvePlaceCompletionIntegers p)
    (b : curvePlaceIntegralClosure L p) (q : CurvePlacesAbove k L p) :
    (integralTensorMap (L := L) p (a ⊗ₜ[p.toValuationSubring] b) q : curvePlaceCompletion q.1) =
      CurvePlaceCompletionExtension.completionMap p q a *
        algebraMap L (curvePlaceCompletion q.1) (b : L) := rfl

/-- The same actual integral tensor map, viewed in the product of completed fields. -/
def integralTensorFieldMap :
    curvePlaceCompletionIntegers p ⊗[p.toValuationSubring] curvePlaceIntegralClosure L p →+*
      (∀ q : CurvePlacesAbove k L p, curvePlaceCompletion q.1) where
  toFun z q := (integralTensorMap (L := L) p z q : curvePlaceCompletion q.1)
  map_one' := by ext q; simp
  map_mul' a b := by ext q; simp
  map_zero' := by ext q; simp
  map_add' a b := by ext q; simp

@[simp]
theorem integralTensorFieldMap_tmul (a : curvePlaceCompletionIntegers p)
    (b : curvePlaceIntegralClosure L p) (q : CurvePlacesAbove k L p) :
    integralTensorFieldMap (L := L) p (a ⊗ₜ[p.toValuationSubring] b) q =
      CurvePlaceCompletionExtension.completionMap p q a *
        algebraMap L (curvePlaceCompletion q.1) (b : L) := rfl

variable [FiniteDimensional K L]

private def fieldBaseChange :
    K ⊗[p.toValuationSubring] curvePlaceIntegralClosure L p ≃ₗ[K] L := by
  let : IsLocalizedModule (nonZeroDivisors p.toValuationSubring)
      (IsScalarTower.toAlgHom p.toValuationSubring (curvePlaceIntegralClosure L p) L).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr
      (IsIntegralClosure.isLocalization p.toValuationSubring K L (curvePlaceIntegralClosure L p))
  exact (IsLocalizedModule.isBaseChange (nonZeroDivisors p.toValuationSubring) K
    (IsScalarTower.toAlgHom p.toValuationSubring (curvePlaceIntegralClosure L p) L).toLinearMap).equiv

omit [Algebra k L] in
private theorem fieldBaseChange_one_tmul (b : curvePlaceIntegralClosure L p) :
    fieldBaseChange (L := L) p (1 ⊗ₜ[p.toValuationSubring] b) = (b : L) := by
  simp [fieldBaseChange, IsBaseChange.equiv_tmul]

/-- Transport the completed-field tensor of the actual integral closure to the field tensor. -/
def fieldTensorTransport :
    curvePlaceCompletion p ⊗[p.toValuationSubring] curvePlaceIntegralClosure L p ≃ₗ[
      curvePlaceCompletion p] curvePlaceCompletion p ⊗[K] L :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange p.toValuationSubring K
    (curvePlaceCompletion p) (curvePlaceCompletion p) (curvePlaceIntegralClosure L p)).symm.trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) (fieldBaseChange p))

omit [Algebra k L] in
@[simp]
theorem fieldTensorTransport_tmul (a : curvePlaceCompletion p)
    (b : curvePlaceIntegralClosure L p) :
    fieldTensorTransport (L := L) p (a ⊗ₜ[p.toValuationSubring] b) = a ⊗ₜ[K] (b : L) := by
  simp [fieldTensorTransport, fieldBaseChange_one_tmul]

/-- The original completed-integer inclusion tensored with the actual integral closure. -/
def integralTensorInclusion :
    curvePlaceCompletionIntegers p ⊗[p.toValuationSubring] curvePlaceIntegralClosure L p →ₗ[
      p.toValuationSubring]
      curvePlaceCompletion p ⊗[p.toValuationSubring] curvePlaceIntegralClosure L p :=
  (Algebra.algHom p.toValuationSubring (curvePlaceCompletionIntegers p)
    (curvePlaceCompletion p)).toLinearMap.rTensor (curvePlaceIntegralClosure L p)

omit [Algebra k L] [FiniteDimensional K L] in
@[simp]
theorem integralTensorInclusion_tmul (a : curvePlaceCompletionIntegers p)
    (b : curvePlaceIntegralClosure L p) :
    integralTensorInclusion (L := L) p (a ⊗ₜ[p.toValuationSubring] b) =
      (a : curvePlaceCompletion p) ⊗ₜ[p.toValuationSubring] b := rfl

omit [Algebra k L] in
/-- Flatness over the original DVR proves injectivity of the integral inclusion. -/
theorem integralTensorInclusion_injective :
    Function.Injective (integralTensorInclusion (L := L) p) := by
  exact Module.Flat.rTensor_preserves_injective_linearMap
    (Algebra.algHom p.toValuationSubring (curvePlaceCompletionIntegers p)
      (curvePlaceCompletion p)).toLinearMap
    (show Function.Injective (algebraMap (curvePlaceCompletionIntegers p)
      (curvePlaceCompletion p)) from Subtype.val_injective)

variable [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] [IsScalarTower k K L]

/-- The field tensor comparison of the original integral closure with all upper completions. -/
def fieldComparison :
    curvePlaceCompletion p ⊗[p.toValuationSubring] curvePlaceIntegralClosure L p ≃ₗ[
      curvePlaceCompletion p] (∀ q : CurvePlacesAbove k L p, curvePlaceCompletion q.1) :=
  (fieldTensorTransport (L := L) p).trans (CurvePlaceCompletedTensorEquiv.allTensorEquiv p).toLinearEquiv

@[simp]
theorem fieldComparison_tmul (a : curvePlaceCompletion p)
    (b : curvePlaceIntegralClosure L p) (q : CurvePlacesAbove k L p) :
    fieldComparison (L := L) p (a ⊗ₜ[p.toValuationSubring] b) q =
      CurvePlaceCompletionExtension.completionMap p q a *
        algebraMap L (curvePlaceCompletion q.1) (b : L) := by
  simp [fieldComparison, fieldTensorTransport_tmul]

/-- The original integral tensor map commutes with the injective field comparison. -/
theorem fieldComparison_inclusion
    (z : curvePlaceCompletionIntegers p ⊗[p.toValuationSubring] curvePlaceIntegralClosure L p) :
    fieldComparison (L := L) p (integralTensorInclusion (L := L) p z) =
      fun q => (integralTensorMap (L := L) p z q : curvePlaceCompletion q.1) := by
  induction z with
  | tmul a b =>
      ext q
      rw [integralTensorInclusion_tmul, fieldComparison_tmul, integralTensorMap_tmul]
  | add z w hz hw =>
      ext q
      simp only [map_add, Pi.add_apply, hz, hw, AddMemClass.coe_add]

/-- The actual integral tensor map is injective, as witnessed in the original field tensor. -/
theorem integralTensorMap_injective : Function.Injective (integralTensorMap (L := L) p) := by
  intro z w h
  apply integralTensorInclusion_injective p
  apply (fieldComparison (L := L) p).injective
  rw [fieldComparison_inclusion, fieldComparison_inclusion, h]

omit [Algebra k L] [FiniteDimensional K L] [Finite k] [Algebra (RatFunc k) K]
  [IsScalarTower k (RatFunc k) K] [FunctionField k K] [IsScalarTower k K L] in
private theorem tensor_coefficients {n : ℕ} (b : Fin n → curvePlaceIntegralClosure L p)
    (hb : Submodule.span p.toValuationSubring (Set.range b) = ⊤)
    (z : curvePlaceCompletionIntegers p ⊗[p.toValuationSubring] curvePlaceIntegralClosure L p) :
    ∃ x : Fin n → curvePlaceCompletionIntegers p, ∑ i, x i ⊗ₜ[p.toValuationSubring] b i = z := by
  classical
  induction z with
  | tmul a y =>
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun p.toValuationSubring).mp
      (show y ∈ Submodule.span p.toValuationSubring (Set.range b) by rw [hb]; trivial)
    refine ⟨fun i => c i • a, ?_⟩
    rw [← hc, TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun i _ => TensorProduct.smul_tmul _ _ _
  | add z w hz hw =>
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, rfl⟩ := hw
    exact ⟨x + y, by simp only [Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]⟩

omit [IsScalarTower k K L] in
/-- Compact finite coefficient spaces make the actual integral tensor image closed. -/
theorem integralTensorFieldMap_range_isClosed :
    IsClosed (Set.range (integralTensorFieldMap (L := L) p)) := by
  classical
  obtain ⟨n, b, hb⟩ :=
    Module.Finite.exists_fin (R := p.toValuationSubring) (M := curvePlaceIntegralClosure L p)
  let f : (Fin n → curvePlaceCompletionIntegers p) →
      (∀ q : CurvePlacesAbove k L p, curvePlaceCompletion q.1) :=
    fun x q => ∑ i, CurvePlaceCompletionExtension.completionMap p q (x i) *
      algebraMap L (curvePlaceCompletion q.1) (b i)
  have hf : Continuous f := by
    apply continuous_pi
    intro q
    exact continuous_finsetSum _ fun i _ =>
      ((CurvePlaceCompletionExtension.continuous_completionMap p q).comp
        (continuous_subtype_val.comp (continuous_apply i))).mul continuous_const
  have he (x : Fin n → curvePlaceCompletionIntegers p) :
      f x = integralTensorFieldMap (L := L) p (∑ i, x i ⊗ₜ[p.toValuationSubring] b i) := by
    ext q
    simp only [map_sum, Finset.sum_apply, integralTensorFieldMap_tmul, f]
  have hr : Set.range f = Set.range (integralTensorFieldMap (L := L) p) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨∑ i, x i ⊗ₜ[p.toValuationSubring] b i, (he x).symm⟩
    · rintro _ ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := tensor_coefficients p b hb z
      exact ⟨x, he x⟩
  let : CompactSpace (curvePlaceCompletionIntegers p) :=
    curvePlaceCompletionIntegers_compactSpace k K p
  rw [← hr]
  exact (isCompact_range hf).isClosed

/-- The actual integral tensor image is the full product of original upper integer rings. -/
theorem integralTensorFieldMap_range :
    Set.range (integralTensorFieldMap (L := L) p) =
      Set.pi Set.univ (fun q : CurvePlacesAbove k L p =>
        (curvePlaceCompletionIntegers q.1 : Set (curvePlaceCompletion q.1))) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩ q _
    exact (integralTensorMap (L := L) p z q).property
  · refine (CurvePlaceIntegralLattice.productIntegers_subset_closure p).trans ?_
    apply closure_minimal _ (integralTensorFieldMap_range_isClosed p)
    rintro _ ⟨b, rfl⟩
    refine ⟨1 ⊗ₜ[p.toValuationSubring] b, ?_⟩
    ext q
    simp [CurvePlaceIntegralLattice.integralEmbedding_apply, integralTensorFieldMap_tmul]

/-- Compactness and proved integral approximation give surjectivity onto all original integers. -/
theorem integralTensorMap_surjective : Function.Surjective (integralTensorMap (L := L) p) := by
  intro x
  have hx : (fun q : CurvePlacesAbove k L p => (x q : curvePlaceCompletion q.1)) ∈
      Set.pi Set.univ (fun q : CurvePlacesAbove k L p =>
        (curvePlaceCompletionIntegers q.1 : Set (curvePlaceCompletion q.1))) :=
    fun q _ => (x q).property
  rw [← integralTensorFieldMap_range p] at hx
  obtain ⟨z, hz⟩ := hx
  refine ⟨z, ?_⟩
  apply funext
  intro q
  apply Subtype.ext
  exact congrFun hz q

/-- The actual completed-integer tensor decomposition, including inseparable extensions. -/
def integralTensorEquiv :
    curvePlaceCompletionIntegers p ⊗[p.toValuationSubring] curvePlaceIntegralClosure L p ≃ₐ[
      curvePlaceCompletionIntegers p]
      (∀ q : CurvePlacesAbove k L p, curvePlaceCompletionIntegers q.1) :=
  AlgEquiv.ofBijective (integralTensorMap p)
    ⟨integralTensorMap_injective p, integralTensorMap_surjective p⟩

@[simp]
theorem integralTensorEquiv_tmul (a : curvePlaceCompletionIntegers p)
    (b : curvePlaceIntegralClosure L p) (q : CurvePlacesAbove k L p) :
    (integralTensorEquiv (L := L) p (a ⊗ₜ[p.toValuationSubring] b) q :
      curvePlaceCompletion q.1) =
        CurvePlaceCompletionExtension.completionMap p q a *
          algebraMap L (curvePlaceCompletion q.1) (b : L) := rfl

@[simp]
theorem integralTensorEquiv_one_tmul (b : curvePlaceIntegralClosure L p)
    (q : CurvePlacesAbove k L p) :
    integralTensorEquiv (L := L) p (1 ⊗ₜ[p.toValuationSubring] b) q =
      algebraMap (curvePlaceIntegralClosure L p) (curvePlaceCompletionIntegers q.1) b := by
  apply Subtype.ext
  simp [integralTensorEquiv_tmul]
  rfl

end Langlands.Global.CurvePlaceIntegralTensor
