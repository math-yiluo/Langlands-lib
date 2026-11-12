import Langlands.GroupScheme.Quaternionic.ScalarInvolution
import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Langlands.GroupScheme.Reductive.Basic

/-!
# The quaternionic Morita isometry statement

Let `D` be a quaternion division algebra over a field `K` with an involution of the first
kind `σ` whose symmetric subspace has dimension `3`, and let `q` be a nondegenerate
`σ`-quadratic form on `D^m` in the sense of Tits. This module states that after base change
to an algebraic closure `L` of `K`, the isometry group scheme `O(q)` becomes isomorphic, as a
group scheme over `Spec L`, to the orthogonal group scheme of a nondegenerate ordinary
quadratic form on `L^(2m)`.
-/

universe u

open CategoryTheory

namespace Langlands.GroupScheme.Quaternionic

/-- Quaternionic Morita comparison for isometry groups: for a quaternion division algebra `D`
over a field `K`, an involution of the first kind `σ` of `D` with `3`-dimensional symmetric
subspace, and a nondegenerate `σ`-quadratic form `q` on `D^m`, there is a nondegenerate
ordinary quadratic form `Q` on `L^(2m)`, `L` an algebraic closure of `K`, such that the base
change of the isometry group scheme `O(q)` to `Spec L` is isomorphic to `O(Q)`. -/
def QuaternionicMoritaIsometryStatement : Prop :=
  ∀ (K D : Type u) [Field K] [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D], Module.finrank K D = 4 →
    ∀ σ : FirstKindInvolution K D, Module.finrank K σ.symmetricSubspace = 3 →
    ∀ (m : ℕ) (q : σ.QuadraticForms (Fin m)), σ.IsNondegenerateQuadratic q →
      ∃ Q : (FirstKindInvolution.scalar (AlgebraicClosure K)).QuadraticForms (Fin (2 * m)),
        (FirstKindInvolution.scalar (AlgebraicClosure K)).IsNondegenerateQuadratic Q ∧
          Nonempty ((GroupScheme.baseChange (toAlgebraicClosure K)).obj (σ.isometryGroup q) ≅
            (FirstKindInvolution.scalar (AlgebraicClosure K)).isometryGroup Q)

end Langlands.GroupScheme.Quaternionic
