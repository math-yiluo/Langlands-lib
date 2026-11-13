import Langlands.GroupScheme.RelativeLevi.Borel
import Langlands.GroupScheme.InnerAutomorphism
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Statement: Borel subgroups are conjugate étale-locally on the base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Borel subgroups are conjugate étale-locally on the base** (Conrad, *Reductive group
schemes* (2014), Theorem 5.2.11(2)). For every reductive group scheme `G` over a scheme `S`
and Borel subgroups `i : B ⟶ G` and `i' : B' ⟶ G` over `S`, there is an étale cover
`{U_j → S}` and, for every `j`, a point `g ∈ G(U_j)` such that conjugating the image of
`B_{U_j}` by `g` gives the image of `B'_{U_j}`, on every test scheme over `U_j`. -/
def RelativeBorelEtaleLocalConjugacyStatement : Prop :=
  ∀ (S : Scheme.{u}) (G B B' : GroupScheme S) (i : B ⟶ G) (i' : B' ⟶ G),
    IsReductive G → IsRelativeBorelSubgroup i → IsRelativeBorelSubgroup i' →
      ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
        ∀ j : 𝒰.I₀, ∃ g : Over.mk (𝟙 (𝒰.X j)) ⟶ ((GroupScheme.baseChange (𝒰.f j)).obj G).X,
          SubgroupFunctor.range ((GroupScheme.baseChange (𝒰.f j)).map i ≫
              (((GroupScheme.baseChange (𝒰.f j)).obj G).innerIso g).hom) =
            SubgroupFunctor.range ((GroupScheme.baseChange (𝒰.f j)).map i')

end Langlands.GroupScheme
