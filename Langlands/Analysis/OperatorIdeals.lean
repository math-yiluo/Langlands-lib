import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Hilbert–Schmidt and trace-class predicates

These definitions use actual Hilbert bases and the positive left modulus of a
bounded operator. Basis independence and the operator-ideal laws are separate
proof obligations.
-/

noncomputable section

namespace Langlands.Analysis.OperatorIdeals

universe u v w

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Square summability on one Hilbert basis, with no chosen basis in the data. -/
def IsHilbertSchmidt (A : E →L[ℂ] F) : Prop :=
  ∃ (s : Set E) (b : HilbertBasis s ℂ E), Summable (fun i => ‖A (b i)‖ ^ 2)

/-- The Hilbert–Schmidt basis sum, followed by the nonnegative real square root.
Its interpretation as a norm requires summability and basis independence. -/
def hilbertSchmidtNormIn {ι : Type w} (b : HilbertBasis ι ℂ E)
    (A : E →L[ℂ] F) : ℝ :=
  Real.sqrt (∑' i, ‖A (b i)‖ ^ 2)

/-- The positive left modulus, following Getz–Hahn's convention `sqrt(A A*)`. -/
def leftModulus (A : E →L[ℂ] E) : E →L[ℂ] E :=
  CFC.sqrt (A * star A)

/-- Summability of the real diagonal of the positive left modulus on one
Hilbert basis. The real part uses Mathlib's inner product convention. -/
def IsTraceClass (A : E →L[ℂ] E) : Prop :=
  ∃ (s : Set E) (b : HilbertBasis s ℂ E),
    Summable (fun i => (inner ℂ (b i) (leftModulus A (b i))).re)

/-- The trace-norm basis sum. Its interpretation as a norm requires
summability and basis independence. -/
def traceNormIn {ι : Type w} (b : HilbertBasis ι ℂ E)
    (A : E →L[ℂ] E) : ℝ :=
  ∑' i, (inner ℂ (b i) (leftModulus A (b i))).re

/-- The complex diagonal sum in a specified basis. Its interpretation as the
operator trace requires summability and basis independence. -/
def traceIn {ι : Type w} (b : HilbertBasis ι ℂ E)
    (A : E →L[ℂ] E) : ℂ :=
  ∑' i, inner ℂ (b i) (A (b i))

end Langlands.Analysis.OperatorIdeals
