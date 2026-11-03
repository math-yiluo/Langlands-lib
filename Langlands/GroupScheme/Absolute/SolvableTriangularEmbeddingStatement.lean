import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Dynamic.GeneralLinearDecomposition

/-! # A closed upper triangular embedding for a smooth connected solvable group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth connected solvable affine group over an algebraically closed field admits a
closed embedding into the concrete upper triangular group scheme. This combines Milne 2017,
Theorem 16.30 with Proposition 16.2(c), using the decreasing weights `i ↦ -i`. -/
def SolvableTriangularEmbeddingStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
    IsSolvableGroupScheme H →
      ∃ (N : ℕ)
        (j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
          (fun i => -(i.val : ℤ))),
        IsClosedSubgroup j

end Langlands.GroupScheme
