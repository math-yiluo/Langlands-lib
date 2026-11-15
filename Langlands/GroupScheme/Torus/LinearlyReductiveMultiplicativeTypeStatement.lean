import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation

/-! # Statement: commutative linearly reductive groups are of multiplicative type (Milne 12.54) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Commutative linearly reductive groups** (Milne, *Algebraic Groups* (2017),
Proposition 12.54). Let `G` be a commutative affine group scheme of finite type over a
field `k`. Then every representation of `G` on `kⁿ` is semisimple (the sum of its simple
stable subspaces is everything) if and only if `G` is of multiplicative type.

This is a statement only; nothing is proved here. -/
def CommutativeLinearlyReductiveMultiplicativeTypeStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
    IsCommMonObj G.X →
      ((∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
          sSup {W : Submodule k (Fin n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
            ∀ U : Submodule k (Fin n → k), ρ.IsStableSubspace U → U ≤ W →
              U = ⊥ ∨ U = W} = ⊤) ↔
        IsMultiplicativeType G)

end Langlands.GroupScheme
