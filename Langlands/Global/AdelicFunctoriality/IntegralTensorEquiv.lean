import Langlands.Global.AdelicFunctoriality.IntegralLocalComparisonProof
import Mathlib.RingTheory.Flat.Domain

/-! # Actual number-field completed-integer tensor equivalence -/

noncomputable section

universe u v

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField TensorProduct
  Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.Global.AdelicFunctoriality

namespace IntegralTensor

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  (p : HeightOneSpectrum (𝓞 K)) (q : FinitePlacesAbove L p)

scoped instance (priority := 50) : Algebra (𝓞 K) (q.1.adicCompletionIntegers L) :=
  ((algebraMap (𝓞 L) (q.1.adicCompletionIntegers L)).comp (algebraMap (𝓞 K) (𝓞 L))).toAlgebra

scoped instance : IsScalarTower (𝓞 K) (𝓞 L) (q.1.adicCompletionIntegers L) :=
  .of_algebraMap_eq fun _ => rfl

scoped instance : IsScalarTower (𝓞 K) (p.adicCompletionIntegers K)
    (q.1.adicCompletionIntegers L) :=
  .of_algebraMap_eq fun r => by
    apply Subtype.ext
    change algebraMap (𝓞 L) (q.1.adicCompletion L) (algebraMap (𝓞 K) (𝓞 L) r) =
      FiniteExtension.completionMap p q.1
        (algebraMap (𝓞 K) (p.adicCompletion K) r)
    simpa only [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) (q.1.adicCompletion L),
      IsScalarTower.algebraMap_apply (𝓞 K) K (p.adicCompletion K),
      IsScalarTower.algebraMap_apply (𝓞 K) K (q.1.adicCompletion L),
      IsScalarTower.algebraMap_apply K L (q.1.adicCompletion L)] using
      (FiniteExtension.completionMap_coe p q.1 (r : K)).symm

/-- The original integral tensor map, with the lower completed integers as coefficient ring. -/
def tensorMap :
    p.adicCompletionIntegers K ⊗[𝓞 K] (𝓞 L) →ₐ[p.adicCompletionIntegers K]
      (∀ q : FinitePlacesAbove L p, q.1.adicCompletionIntegers L) :=
  AlgHom.pi fun q => Algebra.TensorProduct.lift
    (Algebra.ofId (p.adicCompletionIntegers K) (q.1.adicCompletionIntegers L))
    (Algebra.algHom (𝓞 K) (𝓞 L) (q.1.adicCompletionIntegers L)) (fun _ _ => .all _ _)

@[simp]
theorem tensorMap_tmul (a : p.adicCompletionIntegers K) (b : 𝓞 L)
    (q : FinitePlacesAbove L p) :
    (tensorMap (L := L) p (a ⊗ₜ[𝓞 K] b) q : q.1.adicCompletion L) =
      FiniteExtension.completionMap p q.1 a * algebraMap (𝓞 L) (q.1.adicCompletion L) b := by
  change FiniteExtension.completionMap p q.1 a *
    (algebraMap (𝓞 L) (q.1.adicCompletionIntegers L) b : q.1.adicCompletion L) = _
  exact congrArg (fun x => FiniteExtension.completionMap p q.1 a * x)
    (IsScalarTower.algebraMap_apply (𝓞 L) (q.1.adicCompletionIntegers L)
      (q.1.adicCompletion L) b).symm

/-- The new coefficient order preserves the published original comparison. -/
theorem comparison_comm
    (z : p.adicCompletionIntegers K ⊗[𝓞 K] (𝓞 L)) :
    integralTensorComparison L p
        (integralTensorInclusion L p ((TensorProduct.comm (𝓞 K) _ _) z)) =
      fun q => (tensorMap (L := L) p z q : q.1.adicCompletion L) := by
  induction z with
  | tmul a b =>
    ext q
    rw [TensorProduct.comm_tmul, integralTensorComparison_integralTensorInclusion_tmul,
      tensorMap_tmul, FiniteExtension.completionIntegersMap_coe, mul_comm]
  | add z w hz hw =>
    ext q
    simp only [map_add, Pi.add_apply, hz, hw, AddMemClass.coe_add]

omit [NumberField L] in
/-- The published integral inclusion is injective by flatness of the actual ring of integers. -/
theorem inclusion_injective : Function.Injective (integralTensorInclusion L p) := by
  exact Module.Flat.lTensor_preserves_injective_linearMap
    (Algebra.algHom (𝓞 K) (p.adicCompletionIntegers K) (p.adicCompletion K)).toLinearMap
    (show Function.Injective (algebraMap (p.adicCompletionIntegers K) (p.adicCompletion K))
      from Subtype.val_injective)

/-- The actual integer tensor comparison is injective. -/
theorem tensorMap_injective : Function.Injective (tensorMap (L := L) p) := by
  intro z w h
  apply (TensorProduct.comm (𝓞 K) (p.adicCompletionIntegers K) (𝓞 L)).injective
  apply inclusion_injective p
  apply (integralLocalTensorComparison K L p).1.1
  rw [comparison_comm, comparison_comm, h]

/-- The published exact integral image gives every original upper integer tuple. -/
theorem tensorMap_surjective : Function.Surjective (tensorMap (L := L) p) := by
  intro x
  have hx : (fun q : FinitePlacesAbove L p => (x q : q.1.adicCompletion L)) ∈
      Set.pi Set.univ (fun q : FinitePlacesAbove L p =>
        (q.1.adicCompletionIntegers L : Set (q.1.adicCompletion L))) :=
    fun q _ => (x q).property
  rw [← (integralLocalTensorComparison K L p).2.1] at hx
  obtain ⟨z, hz⟩ := hx
  refine ⟨(TensorProduct.comm (𝓞 K) (𝓞 L) (p.adicCompletionIntegers K)) z, ?_⟩
  apply funext
  intro q
  apply Subtype.ext
  have he := congrFun (comparison_comm p
    ((TensorProduct.comm (𝓞 K) (𝓞 L) (p.adicCompletionIntegers K)) z)) q
  rw [TensorProduct.comm_comm] at he
  exact he.symm.trans (congrFun hz q)

/-- The canonical original integral tensor decomposition at every finite number-field place. -/
def tensorEquiv :
    p.adicCompletionIntegers K ⊗[𝓞 K] (𝓞 L) ≃ₐ[p.adicCompletionIntegers K]
      (∀ q : FinitePlacesAbove L p, q.1.adicCompletionIntegers L) :=
  AlgEquiv.ofBijective (tensorMap p) ⟨tensorMap_injective p, tensorMap_surjective p⟩

@[simp]
theorem tensorEquiv_tmul (a : p.adicCompletionIntegers K) (b : 𝓞 L)
    (q : FinitePlacesAbove L p) :
    (tensorEquiv (L := L) p (a ⊗ₜ[𝓞 K] b) q : q.1.adicCompletion L) =
      FiniteExtension.completionMap p q.1 a * algebraMap (𝓞 L) (q.1.adicCompletion L) b :=
  tensorMap_tmul p a b q

@[simp]
theorem tensorEquiv_one_tmul (b : 𝓞 L) (q : FinitePlacesAbove L p) :
    tensorEquiv (L := L) p (1 ⊗ₜ[𝓞 K] b) q =
      algebraMap (𝓞 L) (q.1.adicCompletionIntegers L) b := by
  apply Subtype.ext
  simp only [tensorEquiv_tmul, OneMemClass.coe_one, map_one, one_mul]
  exact IsScalarTower.algebraMap_apply (𝓞 L) (q.1.adicCompletionIntegers L)
    (q.1.adicCompletion L) b

end IntegralTensor

end Langlands.Global.AdelicFunctoriality
