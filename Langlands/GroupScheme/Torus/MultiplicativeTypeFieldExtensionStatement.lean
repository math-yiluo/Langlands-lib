import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.Torus.Split
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Statement: extensions of groups of multiplicative type over a field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Extensions of groups of multiplicative type over a field** (SGA 3, Exposé IX,
Proposition 8.2). Let `k` be a field and let `1 → H → G → K → 1` be a short exact sequence
of `k`-group schemes: `i : H ⟶ G` is a monomorphism and `p : G ⟶ K` is an fppf quotient map
whose kernel is `i(H)`.
1. If `H` and `K` are of multiplicative type and `G` is commutative or `K` is connected,
   then `G` is of multiplicative type.
2. If `H` is diagonalizable (isomorphic to `D_k(Λ)` with `Λ` finitely generated) and `K` is
   a split torus, then `G` is diagonalizable. -/
def MultiplicativeTypeFieldExtensionStatement : Prop :=
  ∀ (k : Type u) [Field k] (H G K : GroupScheme (Spec (CommRingCat.of k)))
    (i : H ⟶ G) (p : G ⟶ K),
    Mono i.hom.hom → RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p →
      (IsMultiplicativeType H → IsMultiplicativeType K →
          (IsCommMonObj G.X ∨ ConnectedSpace K.X.left) → IsMultiplicativeType G) ∧
        ((∃ (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ),
            Nonempty (H ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)) →
          IsSplitTorus K →
          ∃ (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ),
            Nonempty (G ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp))

end Langlands.GroupScheme
