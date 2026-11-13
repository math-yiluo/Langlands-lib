import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.Relative

/-! # Statement: reductive group schemes have maximal tori étale-locally -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Maximal tori exist étale-locally on the base** (Conrad, *Reductive group schemes*
(2014), Corollary 3.2.7, first assertion). For every scheme `S` and every reductive group
scheme `G` over `S` there is an étale cover `{U_j → S}` such that every base change
`G_{U_j}` contains a closed relative torus that is a maximal torus on every residue-field
fibre of `U_j`. -/
def EtaleLocalMaximalTorusExistenceStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
    ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
      ∀ j : 𝒰.I₀, ∃ (T : CommGroupScheme (𝒰.X j))
        (t : T.toGrp ⟶ (GroupScheme.baseChange (𝒰.f j)).obj G),
        RelativeTorus.IsTorus T.toGrp ∧ IsClosedSubgroup t ∧ IsFibrewiseMaximalTorus t

end Langlands.GroupScheme
