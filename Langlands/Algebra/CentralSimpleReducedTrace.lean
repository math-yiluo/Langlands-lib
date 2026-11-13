import Langlands.Algebra.ReducedCharpoly

/-!
# The reduced trace of a finite-dimensional central simple algebra

For a finite-dimensional central simple algebra `A` over a field `K`, the reduced trace
`Trd : A →ₗ[K] K` is minus the coefficient of degree `reducedDegree K A - 1` of the canonical
reduced characteristic polynomial `reducedCharpoly K A a`. Under every splitting chart
`L ⊗[K] A ≃ₐ[L] M_d(L)` it becomes the ordinary matrix trace. The construction works in every
characteristic; it is not the trace of the regular representation, which is `d` times it.
-/

noncomputable section

namespace Langlands.CentralSimple

open scoped TensorProduct

universe u uL

variable (K A : Type u) [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]

/-- The value of the reduced trace: minus the coefficient of degree `reducedDegree K A - 1`
of the reduced characteristic polynomial. -/
def reducedTraceValue (a : A) : K :=
  -(reducedCharpoly K A a).coeff (reducedDegree K A - 1)

/-- Under any splitting chart, the reduced trace becomes the ordinary matrix trace. -/
theorem algebraMap_reducedTraceValue {L : Type uL} [Field L] [Algebra K L]
    (e : L ⊗[K] A ≃ₐ[L]
      Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) L) (a : A) :
    algebraMap K L (reducedTraceValue K A a) = (e (1 ⊗ₜ[K] a)).trace := by
  rw [reducedTraceValue, map_neg, ← Polynomial.coeff_map, reducedCharpoly_map_chart K A e,
    Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]

/-- The reduced trace `Trd : A →ₗ[K] K` of a finite-dimensional central simple algebra. -/
def reducedTraceLinear : A →ₗ[K] K where
  toFun := reducedTraceValue K A
  map_add' a b := by
    let e := finiteGaloisSplittingChart K A
    apply (algebraMap K (finiteGaloisSplittingField K A)).injective
    rw [map_add, algebraMap_reducedTraceValue K A e, algebraMap_reducedTraceValue K A e,
      algebraMap_reducedTraceValue K A e, TensorProduct.tmul_add, map_add, Matrix.trace_add]
  map_smul' t a := by
    let e := finiteGaloisSplittingChart K A
    apply (algebraMap K (finiteGaloisSplittingField K A)).injective
    rw [RingHom.id_apply, smul_eq_mul, map_mul, algebraMap_reducedTraceValue K A e,
      algebraMap_reducedTraceValue K A e, TensorProduct.tmul_smul,
      ← algebraMap_smul (finiteGaloisSplittingField K A) t, map_smul, Matrix.trace_smul,
      smul_eq_mul]

@[simp] theorem reducedTraceLinear_apply (a : A) :
    reducedTraceLinear K A a = -(reducedCharpoly K A a).coeff (reducedDegree K A - 1) :=
  rfl

/-- **Normalization.** For every field extension `L` and every splitting chart
`e : L ⊗[K] A ≃ₐ[L] M_d(L)`, `Trd a` maps to the matrix trace of `e (1 ⊗ a)`. -/
theorem algebraMap_reducedTraceLinear {L : Type uL} [Field L] [Algebra K L]
    (e : L ⊗[K] A ≃ₐ[L]
      Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) L) (a : A) :
    algebraMap K L (reducedTraceLinear K A a) = (e (1 ⊗ₜ[K] a)).trace :=
  algebraMap_reducedTraceValue K A e a

/-- The reduced-trace pairing `(b, a) ↦ Trd (b * a)`, a `K`-bilinear form on `A`. -/
def reducedTracePairing : A →ₗ[K] A →ₗ[K] K :=
  (LinearMap.mul K A).compr₂ (reducedTraceLinear K A)

@[simp] theorem reducedTracePairing_apply (b a : A) :
    reducedTracePairing K A b a = reducedTraceLinear K A (b * a) :=
  rfl

end Langlands.CentralSimple
