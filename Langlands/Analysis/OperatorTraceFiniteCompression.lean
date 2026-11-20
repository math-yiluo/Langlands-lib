import Langlands.Analysis.OperatorTraceProof

/-! # Operator traces of finite-dimensional compressions -/

noncomputable section

open scoped InnerProductSpace BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis.OperatorIdeals

variable {M H : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ M]

/-- Every bounded endomorphism on a finite-dimensional Hilbert space is trace class. -/
theorem isTraceClass_of_finiteDimensional (A : M →L[ℂ] M) : IsTraceClass A := by
  obtain ⟨s, b, _⟩ := exists_hilbertBasis ℂ M
  have : Finite s := b.orthonormal.linearIndependent.finite
  exact ⟨s, b, Summable.of_finite⟩

omit [FiniteDimensional ℂ M] in
/-- An orthonormal basis indexed by a finite type computes the usual diagonal sum. -/
theorem operatorTrace_eq_sum_diagonal {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ M) (A : M →L[ℂ] M) :
    operatorTrace A = ∑ i, ⟪b i, A (b i)⟫_ℂ := by
  let _ : FiniteDimensional ℂ M := b.toBasis.finiteDimensional_of_finite
  rw [(operatorTraceBasis M A ι b.toHilbertBasis (isTraceClass_of_finiteDimensional A)).2,
    traceIn, tsum_fintype]
  simp only [OrthonormalBasis.coe_toHilbertBasis]

/-- The product through a finite-dimensional Hilbert space is trace class, and its trace
is the trace of the reversed product on that space. -/
theorem operatorTrace_finite_compression (i : M →L[ℂ] H) (p : H →L[ℂ] M) :
    IsTraceClass (i.comp p) ∧ operatorTrace (i.comp p) = operatorTrace (p.comp i) := by
  have hh := operatorTraceCyclicity M H (ContinuousLinearMap.id ℂ M) i p
    (isTraceClass_of_finiteDimensional (ContinuousLinearMap.id ℂ M))
  simpa only [ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp] using And.intro hh.1 hh.2.2

end Langlands.Analysis.OperatorIdeals
