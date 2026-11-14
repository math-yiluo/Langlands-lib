import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.RelativeIdentityComponent
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Dynamic.Functoriality

/-! # Statement: normal subgroups of multiplicative type are central -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open RelativeMultiplicativeType in
/-- **Normal subgroups of multiplicative type are central** (Conrad, *Reductive group schemes*
(2014), Lemma 3.3.1). Let `G` be a smooth affine group scheme over a scheme `S` with connected
fibres, and `h : H ⟶ G` a closed subgroup of multiplicative type.
1. If `H` is normal in `G`, then it is central in `G`.
2. If `H` is normal in `G` and `q : G ⟶ Ḡ` is an fppf quotient of `G` by `H`, then for every
   central closed subgroup `H̄'` of `Ḡ` of multiplicative type, the preimage `H'` of `H̄'` in `G`
   (any subgroup representing the preimage functor `q⁻¹(H̄')`) is a central subgroup of `G` of
   multiplicative type. -/
def MultiplicativeTypeNormalCentralStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom],
    (∀ s : S, ConnectedSpace (RelativeIdentityComponent.residueFiber G s).X.left) →
    ∀ (H : GroupScheme S) (h : H ⟶ G), IsClosedSubgroup h → IsMultiplicativeType H →
      (SubgroupFunctor.range h).IsNormal →
      IsCentral h ∧
      ∀ (Q : GroupScheme S) (q : G ⟶ Q),
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range h) q →
        ∀ (H' : GroupScheme S) (h' : H' ⟶ Q), IsClosedSubgroup h' → IsMultiplicativeType H' →
          IsCentral h' →
          ∀ (P : GroupScheme S) (p : P ⟶ G),
            ((SubgroupFunctor.range h').comap q).IsRepresentedBy p →
            IsMultiplicativeType P ∧ IsCentral p

end Langlands.GroupScheme
