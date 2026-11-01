import Langlands.Representation.MatrixCoefficient.CommutingTupleStatement
import Langlands.Representation.MatrixCoefficient.IntegerLatticeProof

/-! # Exponential-polynomial coefficients of commuting invertible tuples -/

set_option autoImplicit false

namespace Langlands

universe u

/-- Renard C.III in the supplied-tuple interface, using the actual product of
all integer powers and one finite expansion valid on the entire lattice. -/
theorem commutingTupleMatrixCoefficientExponentialPolynomial :
    CommutingTupleMatrixCoefficientExponentialPolynomialStatement.{u} := by
  intro d V _ _ _ A v ell
  obtain ⟨l, χ, Q, h⟩ := integerLatticeMatrixCoefficientExponentialPolynomial
    d V (IntegerLattice.tupleRepresentationEquiv d V A) v ell
  refine ⟨l, χ, Q, ?_⟩
  intro n
  have hn := h n
  change ell (IntegerLattice.tupleRepresentationEquiv d V A
    (Multiplicative.ofAdd n) v) = _ at hn
  rw [IntegerLattice.tupleRepresentationEquiv_apply_apply] at hn
  exact hn

end Langlands
