import Langlands.AbelianScheme.Basic
import Langlands.AbelianScheme.Multiplication
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Etale positive multiplication on abelian schemes -/

universe u

open AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Multiplication by a positive integer on an abelian scheme is etale when
the integer is invertible on the base. This is a statement target, not a proof. -/
def MultiplicationEtaleStatement : Prop :=
  ∀ (S : Scheme.{u}) (A : AbelianScheme S) (n : ℕ),
    0 < n → IsUnit (n : Γ(S, ⊤)) →
      Etale (GroupScheme.multiplication A.toGrp (n : ℤ)).hom.hom.left

end Langlands.AbelianScheme
