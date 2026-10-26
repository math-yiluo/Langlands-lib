import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# A balanced nondegenerate pairing on a cyclic polynomial quotient

This module states an internal auxiliary proposition for the proof that every
square matrix over a field is conjugate to its transpose. It supplies no proof.
-/

namespace Langlands

universe uK

/-- Every quotient `K[X]/(q)` for a nonzero polynomial over a field admits a
symmetric nondegenerate bilinear form balanced for multiplication by every
quotient element. Nonzero constant polynomials are included. -/
def CyclicQuotientPairingStatement : Prop :=
  ∀ (K : Type uK) [Field K] (q : Polynomial K), q ≠ 0 →
    ∃ B : LinearMap.BilinForm K (AdjoinRoot q),
      B.IsSymm ∧ B.Nondegenerate ∧
        ∀ (a u v : AdjoinRoot q), B (a * u) v = B u (a * v)

end Langlands
