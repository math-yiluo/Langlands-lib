import Langlands.GroupScheme.Examples.SU3RootParametersRational
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Flat.Basic

/-! # Natural coordinates on the quadratic trace-zero line -/

noncomputable section

universe u v w w'

open Algebra
open scoped TensorProduct

namespace Langlands.GroupScheme.SU3Root

variable (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
  [IsQuadraticExtension k L] [Algebra.IsSeparable k L]

local instance : FiniteDimensional k L :=
  .of_finrank_pos (by rw [IsQuadraticExtension.finrank_eq_two k L]; decide)

variable (η : Parameters.traceZero (fieldInvolution k L)) (hη : (η : L) ≠ 0)

@[simp]
theorem trace_traceZero : Algebra.trace k L (η : L) = 0 := by
  apply (algebraMap k L).injective
  rw [algebraMap_trace, map_zero]
  exact η.property

/-- A nonzero trace-zero scalar and a trace-one scalar form an actual field basis. -/
def traceZeroBasis : Module.Basis (Fin 2) k L :=
  basisOfLinearIndependentOfCardEqFinrank (b := ![traceOne k L, (η : L)]) (by
    rw [linearIndependent_fin2]
    refine ⟨hη, ?_⟩
    intro a ha
    have ht := congrArg (Algebra.trace k L) ha
    exact zero_ne_one (by simpa only [Matrix.cons_val_one, Matrix.cons_val_zero,
      map_smul, trace_traceZero, trace_traceOne, smul_zero] using ht)) (by
    simp [IsQuadraticExtension.finrank_eq_two k L])

@[simp]
theorem traceZeroBasis_zero : traceZeroBasis k L η hη 0 = traceOne k L := by
  simp [traceZeroBasis]

@[simp]
theorem traceZeroBasis_one : traceZeroBasis k L η hη 1 = (η : L) := by
  simp [traceZeroBasis]

section Tensor

variable (R : Type w) [CommRing R] [Algebra k R]

/-- The two coordinates after arbitrary scalar extension, including nonreduced algebras. -/
theorem tensor_traceZeroBasis_decomposition (x : R ⊗[k] L) :
    x = ((traceZeroBasis k L η hη).baseChange R).repr x 0 ⊗ₜ[k] traceOne k L +
      ((traceZeroBasis k L η hη).baseChange R).repr x 1 ⊗ₜ[k] (η : L) := by
  conv_lhs => rw [← ((traceZeroBasis k L η hη).baseChange R).sum_repr x]
  simp [Fin.sum_univ_two, TensorProduct.smul_tmul']

/-- The trace equation on the tensor algebra detects precisely the first basis coordinate. -/
theorem tensor_traceZero_equation (x : R ⊗[k] L) :
    x + (tensorInvolution k L R).bar x =
      ((traceZeroBasis k L η hη).baseChange R).repr x 0 ⊗ₜ[k] (1 : L) := by
  let a := ((traceZeroBasis k L η hη).baseChange R).repr x 0
  let b := ((traceZeroBasis k L η hη).baseChange R).repr x 1
  have hx : x = a ⊗ₜ[k] traceOne k L + b ⊗ₜ[k] (η : L) :=
    tensor_traceZeroBasis_decomposition k L η hη R x
  change x + tensorConjugation k L R x = a ⊗ₜ[k] 1
  rw [hx, map_add, tensorConjugation_tmul, tensorConjugation_tmul]
  calc
    _ = a ⊗ₜ[k] (traceOne k L + conjugation k L (traceOne k L)) +
        b ⊗ₜ[k] ((η : L) + conjugation k L (η : L)) := by
      simp only [TensorProduct.tmul_add]
      abel
    _ = _ := by
      rw [traceOne_add_conjugate,
        show (η : L) + conjugation k L (η : L) = 0 from η.property]
      simp

/-- Multiplication by the chosen nonzero trace-zero scalar parametrizes the entire
trace kernel on every test algebra. -/
def tensorTraceZeroEquiv :
    R ≃+ Parameters.traceZero (tensorInvolution k L R) where
  toFun r := ⟨r ⊗ₜ[k] (η : L), by
    change r ⊗ₜ[k] (η : L) + tensorConjugation k L R (r ⊗ₜ[k] (η : L)) = 0
    rw [tensorConjugation_tmul, ← TensorProduct.tmul_add,
      show (η : L) + conjugation k L (η : L) = 0 from η.property,
      TensorProduct.tmul_zero]⟩
  invFun x := ((traceZeroBasis k L η hη).baseChange R).repr (x : R ⊗[k] L) 1
  left_inv r := by
    change ((traceZeroBasis k L η hη).baseChange R).repr (r ⊗ₜ[k] (η : L)) 1 = r
    rw [Module.Basis.baseChange_repr_tmul]
    have he : (traceZeroBasis k L η hη).repr (η : L) 1 = 1 := by
      simpa only [traceZeroBasis_one, ite_true] using
        (traceZeroBasis k L η hη).repr_self_apply (1 : Fin 2) (1 : Fin 2)
    rw [he, one_smul]
  right_inv x := by
    apply Subtype.ext
    have hx : ((traceZeroBasis k L η hη).baseChange R).repr
        (x : R ⊗[k] L) 0 = 0 := by
      apply Algebra.TensorProduct.includeLeft_injective
        (S := R) (algebraMap k L).injective
      change _ ⊗ₜ[k] (1 : L) = (0 : R) ⊗ₜ[k] (1 : L)
      rw [← tensor_traceZero_equation k L η hη R, x.property,
        TensorProduct.zero_tmul]
    simpa only [hx, TensorProduct.zero_tmul, zero_add] using
      (tensor_traceZeroBasis_decomposition k L η hη R (x : R ⊗[k] L)).symm
  map_add' r s := by
    apply Subtype.ext
    exact TensorProduct.add_tmul r s (η : L)

@[simp]
theorem tensorTraceZeroEquiv_coe (r : R) :
    (tensorTraceZeroEquiv k L η hη R r : R ⊗[k] L) = r ⊗ₜ[k] (η : L) := rfl

end Tensor

section Naturality

variable {R : Type w} {S : Type w'} [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]

/-- The trace-zero coordinate identification commutes with arbitrary coefficient maps. -/
theorem tensorTraceZeroEquiv_naturality (f : R →ₐ[k] S) (r : R) :
    tensorCoefficientMap k L f (tensorTraceZeroEquiv k L η hη R r : R ⊗[k] L) =
      (tensorTraceZeroEquiv k L η hη S (f r) : S ⊗[k] L) := rfl

end Naturality

end Langlands.GroupScheme.SU3Root
