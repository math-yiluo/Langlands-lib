import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.RelativeIdentityComponent
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Statement: reductive fibral identity components are open, closed and of étale index -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Reductive fibral identity components** (Conrad, *Reductive group schemes* (2014),
Proposition 3.1.3). Let `G → S` be a smooth separated group scheme of finite presentation,
and let `i : H ⟶ G` be an open subgroup representing the relative identity component `G⁰`.
Suppose that for every `s ∈ S` the fibre `G⁰_s = H_s` over the residue field `k(s)` is a
connected reductive group. Then `G⁰` is a reductive `S`-group, it is closed (as well as open)
in `G`, and the fppf quotient `G/G⁰` is represented by a separated étale `S`-group of finite
presentation. -/
def IdentityComponentClopenStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [Smooth G.X.hom] [IsSeparated G.X.hom]
    [QuasiCompact G.X.hom] (H : GroupScheme S) (i : H ⟶ G),
    IsRelativeIdentityComponent G i →
    (∀ s : S, IsConnectedReductive (RelativeIdentityComponent.residueFiber H s)) →
      IsReductive H ∧ IsClosedImmersion i.hom.hom.left ∧
        ∃ (E : GroupScheme S) (q : G ⟶ E),
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q ∧
            Etale E.X.hom ∧ IsSeparated E.X.hom ∧ QuasiCompact E.X.hom

end Langlands.GroupScheme
