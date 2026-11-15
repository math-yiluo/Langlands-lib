import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Unipotent normal subgroups and semisimple representations (statement) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Normal unipotent subgroups act trivially on semisimple representations**
(Milne, *Algebraic Groups* (2017), Lemma 19.16 and Proposition 19.17). Let `G` be an affine
group scheme of finite type over a field `k`.

* (Lemma 19.16) If `U` is a unipotent closed subgroup of `G` with normal image, then `U` acts
  trivially on every semisimple finite-dimensional representation of `G`.
* (Proposition 19.17) If `G` is smooth and connected and has a faithful semisimple
  finite-dimensional representation, then the unipotent radical of `G` is trivial.

A finite-dimensional representation is a matrix representation `ρ : G ⟶ GL_n`. Its
subrepresentations are the subspaces `W` of `kⁿ` with `ρ.IsStableSubspace W` (stability tested
over every commutative `k`-algebra). As in Milne's Definition 4.15, `ρ` is semisimple if it is
the sum of its simple subrepresentations: the supremum of the nonzero stable subspaces whose only
stable subspaces are `0` and themselves is all of `kⁿ`. `U` acts trivially when the restriction
`ρ.restrict i = i ≫ ρ` is the trivial representation. Faithful means that `ρ` is a closed
immersion (`IsClosedSubgroup ρ`). -/
def SemisimpleRepresentationUnipotentStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
    let IsSemisimpleRep : (n : ℕ) → MatrixRepresentation G (Fin n) → Prop :=
      fun n ρ => sSup {W : Submodule k (Fin n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
        ∀ U : Submodule k (Fin n → k), ρ.IsStableSubspace U → U ≤ W → U = ⊥ ∨ U = W} = ⊤
    (∀ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G), IsClosedSubgroup i →
        IsUnipotent H → (SubgroupFunctor.range i).IsNormal →
        ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)), IsSemisimpleRep n ρ →
          ρ.restrict i = MatrixRepresentation.trivial H (Fin n)) ∧
      (Smooth G.X.hom → ConnectedSpace G.X.left →
        ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)), IsClosedSubgroup ρ →
          IsSemisimpleRep n ρ → HasTrivialUnipotentRadical G)

end Langlands.GroupScheme
