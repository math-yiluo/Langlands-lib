import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: monic homomorphisms from groups of multiplicative type are closed immersions -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Monic homomorphisms from groups of multiplicative type** (Conrad, *Reductive group
schemes* (2014), Lemma B.1.3; SGA 3, IX, 2.5). Let `G` be an `S`-affine group scheme of finite
presentation over a scheme `S` and `H` an `S`-group of multiplicative type. Every homomorphism
`j : H ⟶ G` whose underlying morphism of `S`-schemes is a monomorphism is a closed
immersion. -/
def MultiplicativeTypeMonoClosedImmersionStatement : Prop :=
  ∀ (S : Scheme.{u}) (G H : GroupScheme S) [IsAffineHom G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] (j : H ⟶ G),
    RelativeMultiplicativeType.IsMultiplicativeType H → Mono j.hom.hom → IsClosedSubgroup j

end Langlands.GroupScheme
