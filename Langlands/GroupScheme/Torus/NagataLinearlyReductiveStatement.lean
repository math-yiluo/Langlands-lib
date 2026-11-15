import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Langlands.GroupScheme.GeometricComponents

/-! # Statement: Nagata's theorem on linearly reductive groups in characteristic `p` -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Nagata's theorem** (Milne, *Algebraic Groups* (2022 corrected reprint), Remark 12.56,
characteristic `p` part). Let `G` be an affine group scheme of finite type over a field `k`
of characteristic `p ≠ 0`. Then every representation of `G` on `kⁿ` is semisimple (the sum
of its simple stable subspaces is everything) if and only if the identity component `G°`
is of multiplicative type and `p` does not divide the index `(G : G°)`.

Here `G°` is given by an open immersion of group schemes `i : H ⟶ G` whose image is the
connected component of the identity point, and `(G : G°)` is the number of connected
components of the base change of `G` to an algebraic closure of `k`.

This is a statement only; nothing is proved here. -/
def NagataLinearlyReductiveStatement : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p], p ≠ 0 →
    ∀ (G : GroupScheme (Spec (CommRingCat.of k)))
      [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
      ((∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
          sSup {W : Submodule k (Fin n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
            ∀ U : Submodule k (Fin n → k), ρ.IsStableSubspace U → U ≤ W →
              U = ⊥ ∨ U = W} = ⊤) ↔
        ((∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
            IsOpenImmersion i.hom.hom.left ∧
            Set.range i.hom.hom.left = IdentityComponent.identitySet G ∧
            IsMultiplicativeType H) ∧
          ¬ p ∣ Nat.card (IdentityComponent.GeometricComponents k G)))

end Langlands.GroupScheme
