import Langlands.AbelianScheme.IsogenySpecialization
import Langlands.AbelianScheme.AlgClosedIsogenyPoints
import Langlands.AbelianScheme.Tate.RationalPrimeHom
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Determinant

/-! # The `p`-adic size of the kernel of an isogeny -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

/-- Let `α` be an isogeny from an abelian scheme `A` over an algebraically closed field `k`
to itself, and let `p` be a prime different from the characteristic of `k`. The `p`-adic
norm of the number of `k`-points of the kernel of `α` equals the `p`-adic norm of the
determinant of the actual rational `p`-adic Tate map of `α`. This proposition is a
statement target, not a proof. -/
def IsogenyKernelCardTateDeterminantStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (p : ℕ) [Fact p.Prime], (p : k) ≠ 0 →
    ∀ α : A ⟶ A, IsIsogeny α →
      ‖((Nat.card (GroupScheme.pointsHom (groupHom α) (Over.mk (𝟙 _))).ker : ℕ) : ℚ_[p])‖ =
        ‖LinearMap.det (Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p α)‖

end Langlands.AbelianScheme
