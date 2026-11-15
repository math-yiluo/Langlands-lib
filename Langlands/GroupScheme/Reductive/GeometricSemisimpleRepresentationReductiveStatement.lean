import Langlands.GroupScheme.Rational.ValuedRepresentationBaseChange
import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Langlands.GroupScheme.Reductive.Basic

/-! # A geometrically semisimple faithful representation forces reductivity (statement) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **A connected group variety with a faithful representation that stays semisimple over an
algebraic closure is reductive** (Milne, *Algebraic Groups* (2017), Corollary 19.18). Let `G`
be a smooth connected affine group scheme over a field `k`, and let `ρ : G ⟶ GL_n` be a faithful
(closed immersion) finite-dimensional representation that is semisimple and whose base change
`ρ_{k^a}` to an algebraic closure `k^a` of `k` is semisimple. Then `G` is connected reductive.

As in Milne's Definition 4.15, a representation is semisimple if it is the sum of its simple
subrepresentations (stable subspaces). -/
def GeometricallySemisimpleRepresentationReductiveStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom],
    Smooth G.X.hom → ConnectedSpace G.X.left →
    let IsSemisimpleRep : {F : Type u} → [Field F] →
        {H : GroupScheme (Spec (CommRingCat.of F))} → (n : ℕ) →
        MatrixRepresentation H (Fin n) → Prop :=
      fun {F} _ {_} n σ => sSup {W : Submodule F (Fin n → F) | σ.IsStableSubspace W ∧ W ≠ ⊥ ∧
        ∀ U : Submodule F (Fin n → F), σ.IsStableSubspace U → U ≤ W → U = ⊥ ∨ U = W} = ⊤
    ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)), IsClosedSubgroup ρ →
      IsSemisimpleRep n ρ → IsSemisimpleRep n (ρ.baseChange (toAlgebraicClosure k)) →
      IsConnectedReductive G

end Langlands.GroupScheme
