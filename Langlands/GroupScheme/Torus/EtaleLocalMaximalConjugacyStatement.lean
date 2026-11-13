import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.InnerAutomorphism

/-! # Statement: maximal tori are conjugate étale-locally on the base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Maximal tori are conjugate étale-locally on the base** (Conrad, *Reductive group
schemes* (2014), Theorem 3.2.6, last assertion, in the generality used by its proof). For
every scheme `S`, every group scheme `G` over `S` with smooth affine structure morphism, and
closed relative tori `t : T ⟶ G` and `t' : T' ⟶ G` that are maximal tori on every
residue-field fibre, there is an étale cover `{U_j → S}` and, for every `j`, a point
`g ∈ G(U_j)` such that conjugating the image of `t` by `g` gives the image of `t'`, on every
test scheme over `U_j`. -/
def EtaleLocalMaximalTorusConjugacyStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (T T' : CommGroupScheme S) (t : T.toGrp ⟶ G) (t' : T'.toGrp ⟶ G),
    RelativeTorus.IsTorus T.toGrp → IsClosedSubgroup t → IsFibrewiseMaximalTorus t →
    RelativeTorus.IsTorus T'.toGrp → IsClosedSubgroup t' → IsFibrewiseMaximalTorus t' →
      ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
        ∀ j : 𝒰.I₀, ∃ g : Over.mk (𝟙 (𝒰.X j)) ⟶ ((GroupScheme.baseChange (𝒰.f j)).obj G).X,
          SubgroupFunctor.range ((GroupScheme.baseChange (𝒰.f j)).map t ≫
              (((GroupScheme.baseChange (𝒰.f j)).obj G).innerIso g).hom) =
            SubgroupFunctor.range ((GroupScheme.baseChange (𝒰.f j)).map t')

end Langlands.GroupScheme
