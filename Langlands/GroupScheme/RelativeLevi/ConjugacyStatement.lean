import Langlands.GroupScheme.RelativeLevi.Basic
import Langlands.GroupScheme.InnerAutomorphism

/-! # Statement: Levi subgroups are conjugate under a unique point of the unipotent radical -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Conjugacy of Levi subgroups** (Conrad, *Reductive group schemes* (2014),
Corollary 5.4.6, torsor assertion). For every scheme `S`, reductive group scheme `G` over
`S`, parabolic subgroup `i : P ⟶ G` with unipotent radical `r : U ⟶ P`, and Levi subgroups
`l : L ⟶ P` and `l' : L' ⟶ P`, there is exactly one point `u ∈ U(S)` such that the image
of `l'` equals the image of `l` conjugated by `r(u)`, on every test scheme. -/
def RelativeLeviConjugacyStatement : Prop :=
  ∀ (S : Scheme.{u}) (G P U L L' : GroupScheme S) (i : P ⟶ G) (r : U ⟶ P)
    (l : L ⟶ P) (l' : L' ⟶ P),
    IsReductive G → IsRelativeParabolicSubgroup i → IsRelativeUnipotentRadical r →
    IsRelativeLeviSubgroup l → IsRelativeLeviSubgroup l' →
      ∃! u : Over.mk (𝟙 S) ⟶ U.X,
        SubgroupFunctor.range l' =
          SubgroupFunctor.range (l ≫ (P.innerIso (u ≫ r.hom.hom)).hom)

end Langlands.GroupScheme
