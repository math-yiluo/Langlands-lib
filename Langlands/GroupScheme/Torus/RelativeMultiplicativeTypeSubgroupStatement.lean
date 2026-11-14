import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: fppf closed subgroups of groups of multiplicative type -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Closed subgroups of multiplicative type groups** (Conrad, *Reductive group schemes*
(2014), Corollary B.3.3). Let `H'` be a group of multiplicative type over a scheme `S`. Every
closed subgroup `H ⊂ H'` that is flat and locally of finite presentation over `S` is of
multiplicative type. -/
def RelativeMultiplicativeTypeClosedSubgroupStatement : Prop :=
  ∀ (S : Scheme.{u}) (H H' : GroupScheme S) (i : H ⟶ H'),
    RelativeMultiplicativeType.IsMultiplicativeType H' → IsClosedSubgroup i →
    Flat H.X.hom → LocallyOfFinitePresentation H.X.hom →
    RelativeMultiplicativeType.IsMultiplicativeType H

end Langlands.GroupScheme
