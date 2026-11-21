import Langlands.LinearAlgebra.FiniteRankTrace
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Finite

/-! # Multiplicativity of trace on finite tensor products of finite-rank maps -/

noncomputable section

namespace Langlands

open scoped TensorProduct

universe u v w

section FiniteDimensional

variable {k : Type u} [Field k] {ι : Type v} [Fintype ι]
variable {V : ι → Type w} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
variable [∀ i, FiniteDimensional k (V i)]

/-- The trace of the tensor endomorphism is the product of the traces. -/
theorem trace_map_piTensorProduct (T : ∀ i, Module.End k (V i)) :
    LinearMap.trace k (⨂[k] i, V i) (PiTensorProduct.map T) =
      ∏ i, LinearMap.trace k (V i) (T i) := by
  classical
  let b (i : ι) := Module.finBasis k (V i)
  rw [LinearMap.trace_eq_matrix_trace k (Basis.piTensorProduct b)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
    Basis.piTensorProduct_repr_tprod_apply]
  rw [← Fintype.prod_sum (fun (i : ι) (j : Fin (Module.finrank k (V i))) =>
    (b i).repr (T i (b i j)) j)]
  apply Finset.prod_congr rfl
  intro i _
  rw [LinearMap.trace_eq_matrix_trace k (b i)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]

end FiniteDimensional

namespace FiniteRankEnd

variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- The tensor of a finite family of finite-rank endomorphisms factors through
 the tensor of their finite-dimensional ranges. -/
def piTensorMap (T : ∀ i, finiteRankEnd (V i)) : finiteRankEnd (⨂[ℂ] i, V i) :=
  ofFactorization (PiTensorProduct.map fun i => (T i).val.rangeRestrict)
    (PiTensorProduct.map fun i => (T i).val.range.subtype)

@[simp]
theorem piTensorMap_val (T : ∀ i, finiteRankEnd (V i)) :
    (piTensorMap T).val = PiTensorProduct.map (fun i => (T i).val) := by
  change (PiTensorProduct.map fun i => (T i).val.range.subtype).comp
    (PiTensorProduct.map fun i => (T i).val.rangeRestrict) = _
  rw [← PiTensorProduct.map_comp]
  congr 1

/-- Finite-rank trace is multiplicative for the tensor of a finite family. -/
@[simp]
theorem trace_piTensorMap (T : ∀ i, finiteRankEnd (V i)) :
    trace (piTensorMap T) = ∏ i, trace (T i) := by
  rw [piTensorMap, trace_ofFactorization, ← PiTensorProduct.map_comp, trace_map_piTensorProduct]
  rfl

end FiniteRankEnd

end Langlands
