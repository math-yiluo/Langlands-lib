import Langlands.GroupScheme.RelativeLevi.Basic

/-! # Statement: existence and uniqueness of the unipotent radical of a parabolic subgroup -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **The unipotent radical of a parabolic subgroup** (Conrad, *Reductive group schemes*
(2014), Corollary 5.2.5, first assertion). For every scheme `S`, reductive group scheme `G`
over `S` and parabolic subgroup `i : P ⟶ G`, there is a closed subgroup `r : U ⟶ P`
satisfying `IsRelativeUnipotentRadical`, and every other such subgroup has the same image
as `r` on every test scheme. -/
def RelativeUnipotentRadicalStatement : Prop :=
  ∀ (S : Scheme.{u}) (G P : GroupScheme S) (i : P ⟶ G),
    IsReductive G → IsRelativeParabolicSubgroup i →
      ∃ (U : GroupScheme S) (r : U ⟶ P), IsRelativeUnipotentRadical r ∧
        ∀ (U' : GroupScheme S) (r' : U' ⟶ P), IsRelativeUnipotentRadical r' →
          SubgroupFunctor.range r' = SubgroupFunctor.range r

end Langlands.GroupScheme
