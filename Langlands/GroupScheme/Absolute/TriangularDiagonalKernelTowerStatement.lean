import Langlands.GroupScheme.Dynamic.GeneralLinearDecomposition
import Langlands.GroupScheme.LinearKernelTower
import Langlands.GroupScheme.Torus.Diagonalizable
import Mathlib.GroupTheory.Finiteness

/-! # Character-linear kernel towers for actual triangular diagonal images -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over any field, an affine locally finite type closed triangular subgroup admits a finite
character-linear kernel tower for every supplied closed fppf diagonal-image factorization
through `D(Λ)`, with `Λ` finitely generated. This is the quotient-oriented reformulation of
Milne (2022), Theorem 16.21 and its proof, for the actual diagonal projection and the given
structural map `q`. No smoothness, connectedness or splitting is assumed. -/
def TriangularDiagonalKernelTowerStatement : Prop :=
  ∀ (k : Type u) [Field k]
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
      ∀ (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ],
        let D := Diagonalizable.groupScheme (CommRingCat.of k) Λ
        ∀ (q : H ⟶ D.toGrp) (d : D.toGrp ⟶ L),
          IsClosedSubgroup d →
            q ≫ d = f →
              RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι f)) q →
                LinearKernelTower.AdmitsTower D q

end Langlands.GroupScheme
