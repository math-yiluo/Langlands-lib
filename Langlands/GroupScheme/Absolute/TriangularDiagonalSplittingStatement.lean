import Langlands.GroupScheme.Dynamic.GeneralLinearDecomposition
import Langlands.GroupScheme.Reductive.Basic

/-! # Splitting of the diagonal image of a triangular subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For an affine, locally finite type closed subgroup `H` of the upper triangular group over
an algebraically closed field, the diagonal projection `f : H ⟶ D_N` factors as `q ≫ d`
through a closed subgroup `d : D ⟶ D_N`, and `q : H ⟶ D` has a group-scheme section `s`.
Here `D` is the actual diagonal image, and `s` is the splitting of Milne 2017, 16.26(a),
after 16.2(c)⇒(d), 16.6 and 16.8 identify the diagonal kernel with the canonical
unipotent part. -/
def TriangularDiagonalSplittingStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType H.X.hom] [IsAffineHom H.X.hom]
    (N : ℕ)
    (j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ))),
    IsClosedSubgroup j →
      let L := GeneralLinear.blockLeviScheme (Fin N) (CommRingCat.of k)
        (fun i => -(i.val : ℤ))
      let f : H ⟶ L := j ≫ GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k)
        (fun i => -(i.val : ℤ))
      ∃ (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ L) (q : H ⟶ D) (s : D ⟶ H),
        IsClosedSubgroup d ∧ q ≫ d = f ∧ s ≫ q = 𝟙 D

end Langlands.GroupScheme
