import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Langlands.GroupScheme.Rational.SplitTorus

/-!
# Split rank of `O(q)⁰` equals the Witt index

This unproved statement says that, over every field, the split rank of the connected
isometry group of a nondegenerate `σ`-quadratic form over a central division algebra with
an involution of the first kind of type `1` equals the Witt index of the form.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Quaternionic

/-- Let `D` be a finite-dimensional central division algebra of degree `degree` over a
field `K`, `σ` an involution of the first kind of `D` whose symmetric subspace has dimension
`degree * (degree + 1) / 2` (Tits type `1`), and `q` a nondegenerate `σ`-quadratic form on `D^n`
whose isometry group `O(q)` is smooth. Then the split rank of `O(q)⁰` is the Witt index of
`q`. -/
def ConnectedIsometrySplitRankStatement : Prop :=
  ∀ (K D : Type u) [Field K] [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] (degree : ℕ), Module.finrank K D = degree ^ 2 →
    ∀ (σ : FirstKindInvolution K D),
    Module.finrank K σ.symmetricSubspace = degree * (degree + 1) / 2 →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (q : σ.QuadraticForms n)
    [Smooth (σ.isometryGroup q).X.hom],
    σ.IsNondegenerateQuadratic q →
      splitRank (σ.connectedIsometryGroup q) = σ.quadraticWittIndex q

end Langlands.GroupScheme.Quaternionic
