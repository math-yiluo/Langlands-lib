import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Langlands.GroupScheme.Rational.SplitTorus

/-! # The split rank of the symplectic group of an antihermitian form is its Witt index:
statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Let `D` be a central division algebra of degree `degree` over a field `K`, with an
involution of the first kind `σ` whose symmetric space has dimension
`degree * (degree + 1) / 2`, and let `H ∈ M_m(D)`, `m ≠ 0`, be an invertible trace-valued
`σ`-antihermitian Gram matrix. Then the split rank of the symplectic group `σ.symplecticGroup H`
equals the Witt index of the form with Gram matrix `H`. -/
def AntihermitianSymplecticSplitRankStatement : Prop :=
  ∀ (K : Type u) [Field K] (D : Type u) [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [FiniteDimensional K D] (degree m : ℕ) [NeZero m]
    (σ : Quaternionic.FirstKindInvolution K D) (H : Matrix (Fin m) (Fin m) D),
    Module.finrank K D = degree ^ 2 →
    Module.finrank K σ.symmetricSubspace = degree * (degree + 1) / 2 →
    σ.IsAntihermitian H → IsUnit H →
      splitRank (σ.symplecticGroup H) = σ.wittIndex H

end Langlands.GroupScheme
