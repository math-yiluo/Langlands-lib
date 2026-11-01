import Langlands.Representation.IntegerLattice
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Exponential-polynomial coefficients of commuting invertible tuples -/

set_option autoImplicit false

namespace Langlands

universe u

/-- Renard C.III in its original tuple formulation: one finite family of
characters and ordinary polynomials expands the coefficient of the actual
integer-power product on the entire integer lattice. -/
def CommutingTupleMatrixCoefficientExponentialPolynomialStatement : Prop :=
  ∀ (d : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : IntegerLattice.CommutingInvertibleTuple d V)
    (v : V) (ell : Module.Dual ℂ V),
    ∃ (l : ℕ) (χ : Fin l → IntegerLattice.Lattice d →* ℂˣ)
      (Q : Fin l → MvPolynomial (Fin d) ℂ),
      ∀ n : Fin d → ℤ,
        ell (((Finset.univ.noncommProd (fun i => A.1 i ^ n i)
          (fun _ _ _ _ hij => (A.2 hij).zpow_zpow _ _) :
            (Module.End ℂ V)ˣ) : Module.End ℂ V) v) =
          ∑ j, (χ j (Multiplicative.ofAdd n) : ℂ) *
            MvPolynomial.eval (fun i => (n i : ℂ)) (Q j)

end Langlands
