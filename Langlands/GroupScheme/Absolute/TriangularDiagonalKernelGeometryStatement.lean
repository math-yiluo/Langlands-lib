import Langlands.GroupScheme.Dynamic.GeneralLinearDecomposition

/-! # Geometry of the diagonal kernel of a triangular subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For a smooth connected affine closed subgroup of the upper triangular group over an
algebraically closed field, the scheme-theoretic kernel of the diagonal projection is smooth
and connected. This is the concrete-kernel specialization of Milne 2017, 16.10, using
16.2(c)⇒(d), 16.6, 16.8 and 16.26(a). -/
def TriangularDiagonalKernelGeometryStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (N : ℕ)
    (j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ))),
    IsClosedSubgroup j →
      let f := j ≫ GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k)
        (fun i => -(i.val : ℤ))
      Smooth (kernel f).X.hom ∧ ConnectedSpace (kernel f).X.left

end Langlands.GroupScheme
