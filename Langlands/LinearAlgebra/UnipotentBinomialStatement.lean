import Mathlib.Algebra.Module.End
import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.Binomial

/-! # Finite binomial expansions for integer powers of unipotent operators -/

namespace Langlands

universe u

/-- The finite binomial formula used in Renard C.III, including every negative
integer exponent and the zero-dimensional carrier. This is a statement. -/
def IntegerUnipotentBinomialStatement : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V]
    (g : (Module.End ℂ V)ˣ) (r : ℕ),
    ((g : Module.End ℂ V) - 1) ^ r = 0 →
    ∀ n : ℤ,
      ((g ^ n : (Module.End ℂ V)ˣ) : Module.End ℂ V) =
        ∑ j ∈ Finset.range r,
          Ring.choose (n : ℂ) j • ((g : Module.End ℂ V) - 1) ^ j

/-- The scalar coefficients in the finite binomial formula are evaluations of
explicit complex polynomials. This is a statement, not a proof. -/
def ComplexBinomialCoefficientPolynomialStatement : Prop :=
  ∀ (j : ℕ) (z : ℂ),
    Polynomial.eval z
      ((j.factorial : ℂ)⁻¹ • descPochhammer ℂ j) =
        Ring.choose z j

/-- Both auxiliary assertions of the Renard C.III proof, packaged as one
statement target. -/
def RenardCIIIUnipotentBinomialStatement : Prop :=
  IntegerUnipotentBinomialStatement.{u} ∧
    ComplexBinomialCoefficientPolynomialStatement

end Langlands
