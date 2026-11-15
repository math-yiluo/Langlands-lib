import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Langlands.GroupScheme.MatrixRepresentationTensor
import Langlands.GroupScheme.IdentityComponent
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Semisimple representations and the identity component in characteristic zero (statement) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Semisimple representations in characteristic zero: the identity component and tensor
products** (Milne, *Algebraic Groups* (2017), Corollaries 22.43 and 22.44). Let `G` be an affine
group scheme of finite type over a field `k` of characteristic zero.

* (Corollary 22.43) If `G` is smooth, then every finite-dimensional representation of `G` is
  semisimple if and only if the identity component `G⁰` is connected reductive.
* (Corollary 22.44) The tensor product of two semisimple finite-dimensional representations of
  `G` is semisimple.

A finite-dimensional representation is a matrix representation `ρ : G ⟶ GL_ι` for a finite
index type `ι`. Its subrepresentations are the subspaces `W` of `k^ι` with
`ρ.IsStableSubspace W` (stability tested over every commutative `k`-algebra). As in Milne's
Definition 4.15, `ρ` is semisimple if it is the sum of its simple subrepresentations: the
supremum of the nonzero stable subspaces whose only stable subspaces are `0` and themselves is
all of `k^ι`. Smoothness is needed to form `identityComponent G`; in characteristic zero every
affine group scheme of finite type over `k` is smooth (Cartier). -/
def CharZeroSemisimpleRepresentationIdentityComponentStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
    let IsSemisimpleRep : (ι : Type) → [Fintype ι] → [DecidableEq ι] →
        MatrixRepresentation G ι → Prop :=
      fun ι _ _ ρ => sSup {W : Submodule k (ι → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
        ∀ U : Submodule k (ι → k), ρ.IsStableSubspace U → U ≤ W → U = ⊥ ∨ U = W} = ⊤
    (∀ [Smooth G.X.hom],
        (∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)), IsSemisimpleRep (Fin n) ρ) ↔
          IsConnectedReductive (identityComponent G)) ∧
      ∀ (n m : ℕ) (ρ : MatrixRepresentation G (Fin n)) (σ : MatrixRepresentation G (Fin m)),
        IsSemisimpleRep (Fin n) ρ → IsSemisimpleRep (Fin m) σ →
          IsSemisimpleRep (Fin n × Fin m) (ρ.tensor σ)

end Langlands.GroupScheme
