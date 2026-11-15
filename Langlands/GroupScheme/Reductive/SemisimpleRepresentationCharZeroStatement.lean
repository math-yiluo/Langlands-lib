import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Reductive groups in characteristic zero and semisimple representations (statement) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Characteristic zero: reductive groups are those with semisimple representations**
(Milne, *Algebraic Groups* (2017), Theorem 22.42). For every field `k` of characteristic zero
and every connected affine group scheme `G` of finite type over `k`, the following are
equivalent: `G` is connected reductive; every finite-dimensional representation of `G` is
semisimple; some faithful finite-dimensional representation of `G` is semisimple.

A finite-dimensional representation is a matrix representation `ρ : G ⟶ GL_n`. Its
subrepresentations are the subspaces `W` of `kⁿ` with `ρ.IsStableSubspace W` (stability tested
over every commutative `k`-algebra). As in Milne's Definition 4.15, `ρ` is semisimple if it is
the sum of its simple subrepresentations: the supremum of the nonzero stable subspaces whose only
stable subspaces are `0` and themselves is all of `kⁿ`. Faithful means that `ρ` is a closed
immersion (`IsClosedSubgroup ρ`). -/
def CharZeroReductiveSemisimpleRepresentationStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
    ConnectedSpace G.X.left →
    let IsSemisimpleRep : (n : ℕ) → MatrixRepresentation G (Fin n) → Prop :=
      fun n ρ => sSup {W : Submodule k (Fin n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
        ∀ U : Submodule k (Fin n → k), ρ.IsStableSubspace U → U ≤ W → U = ⊥ ∨ U = W} = ⊤
    (IsConnectedReductive G ↔
        ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)), IsSemisimpleRep n ρ) ∧
      (IsConnectedReductive G ↔
        ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
          IsClosedSubgroup ρ ∧ IsSemisimpleRep n ρ)

end Langlands.GroupScheme
