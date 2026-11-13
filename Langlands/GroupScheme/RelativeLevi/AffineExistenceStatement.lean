import Langlands.GroupScheme.RelativeLevi.Basic

/-! # Statement: parabolic subgroups over affine schemes have Levi subgroups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Existence of Levi subgroups over an affine base** (Conrad, *Reductive group schemes*
(2014), Corollary 5.4.8, existence assertion). For every affine scheme `S`, reductive group
scheme `G` over `S` and parabolic subgroup `i : P ⟶ G`, there is a Levi subgroup
`l : L ⟶ P`. -/
def RelativeLeviAffineExistenceStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsAffine S] (G P : GroupScheme S) (i : P ⟶ G),
    IsReductive G → IsRelativeParabolicSubgroup i →
      ∃ (L : GroupScheme S) (l : L ⟶ P), IsRelativeLeviSubgroup l

end Langlands.GroupScheme
