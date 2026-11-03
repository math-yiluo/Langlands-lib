import Langlands.GroupScheme.Reductive.Basic
import Langlands.AbelianScheme.Kernel

/-! # Levi decompositions in characteristic zero

The theorem of Mostow (Milne, *Algebraic Groups*, 25.48–25.49): over a field of characteristic
zero, every smooth connected affine group scheme of finite type is a semidirect product of its
unipotent radical by a connected reductive Levi subgroup. It is stated here as a split
homomorphism onto a connected reductive group whose scheme-theoretic kernel is smooth,
connected and unipotent.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Levi decomposition in characteristic zero** (Mostow; Milne, *Algebraic Groups*,
25.48–25.49). For every field `F` of characteristic zero and every smooth connected affine
group scheme `G` of finite type over `F`, there are a connected reductive group `L` over `F`
and homomorphisms `p : G ⟶ L`, `j : L ⟶ G` with `j ≫ p = 𝟙 L` such that the
scheme-theoretic kernel of `p` is smooth, connected and unipotent. This proposition is a
target and supplies no proof. -/
def CharacteristicZeroLeviDecompositionStatement : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    Smooth G.X.hom → ConnectedSpace G.X.left →
      ∃ (L : GroupScheme (Spec (CommRingCat.of F))) (p : G ⟶ L) (j : L ⟶ G),
        j ≫ p = 𝟙 L ∧ IsConnectedReductive L ∧
          Smooth (kernel p).X.hom ∧ ConnectedSpace (kernel p).X.left ∧
            IsUnipotent (kernel p)

end Langlands.GroupScheme
