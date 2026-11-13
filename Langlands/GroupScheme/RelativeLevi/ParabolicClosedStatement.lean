import Langlands.GroupScheme.RelativeLevi.Basic

/-! # Statement: parabolic subgroups of reductive group schemes are closed -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Parabolic subgroups are closed** (Conrad, *Reductive group schemes* (2014),
Proposition 5.2.3, first assertion). For every scheme `S`, reductive group scheme `G`
over `S` and parabolic subgroup `i : P ⟶ G` in the sense of `IsRelativeParabolicSubgroup`,
the monomorphism `i` is a closed immersion. -/
def RelativeParabolicClosedStatement : Prop :=
  ∀ (S : Scheme.{u}) (G P : GroupScheme S) (i : P ⟶ G),
    IsReductive G → IsRelativeParabolicSubgroup i → IsClosedSubgroup i

end Langlands.GroupScheme
