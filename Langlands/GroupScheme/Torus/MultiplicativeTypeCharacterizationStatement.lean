import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.VectorGroupQuotient
import Langlands.GroupScheme.AffineHopfCoordinates
import Langlands.RingTheory.Coalgebra.Subcoalgebra.Basic
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.RingTheory.Etale.Basic
import Mathlib.FieldTheory.IsSepClosed

/-! # Statement: characterizations of groups of multiplicative type over a field (Milne 12.18) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Characterizations of groups of multiplicative type** (Milne, *Algebraic Groups* (2017),
Theorem 12.18). Let `G` be an affine group scheme of finite type over a field `k` and let `Ks`
be a separable closure of `k`. The following are equivalent:

* (a) `G` is of multiplicative type (`IsMultiplicativeType G`);
* (b) `G` is commutative and every homomorphism `G ⟶ 𝔾ₐ` is trivial;
* (c) `G` is commutative and its coordinate coalgebra `O(G)` is coétale: every element of
  `O(G)` lies in a finite-dimensional cocommutative subcoalgebra `D` whose convolution dual
  `D^∨` is an étale `k`-algebra;
* (d) `G` becomes diagonalizable over `Ks`: the base change `G_{Ks}` is isomorphic to
  `D_{Ks}(Λ)` for a finitely generated abelian group `Λ`.

This is a statement only; nothing is proved here. -/
def MultiplicativeTypeCharacterizationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    (Ks : Type u) [Field Ks] [Algebra k Ks] [IsSepClosure k Ks],
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    [IsMultiplicativeType G,
      IsCommMonObj G.X ∧ Subsingleton (G ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1),
      IsCommMonObj G.X ∧
        ∀ c : AffineCoordinates.hopfAlgebra G,
          ∃ D : Subcoalgebra k (AffineCoordinates.hopfAlgebra G),
            c ∈ D ∧ FiniteDimensional k D ∧
              ∃ _ : Coalgebra.IsCocomm k D, Algebra.Etale k (WithConv (D →ₗ[k] k)),
      ∃ (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ),
        Nonempty (((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k Ks)))).obj G) ≅
            (Diagonalizable.groupScheme (CommRingCat.of Ks) Λ).toGrp)].TFAE

end Langlands.GroupScheme
