import Langlands.GroupScheme.RelativeLevi.Basic
import Langlands.GroupScheme.InnerAutomorphism
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Statement: parabolic subgroups conjugate at a point are conjugate étale-locally -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Parabolic subgroups conjugate at a point are conjugate near it** (Conrad, *Reductive
group schemes* (2014), Corollary 5.2.7(1), first assertion). Let `G` be a reductive group
scheme over a scheme `S`, let `i : P ⟶ G` and `j : Q ⟶ G` be parabolic subgroups in the sense
of `IsRelativeParabolicSubgroup`, and let `s` be a point of `S`. Suppose that some point
`g ∈ G(κ(s))` of the residue-field fibre conjugates the image of `i_s` onto the image of `j_s`
on every test scheme. Then there are an étale morphism `f : U ⟶ S` whose image contains `s`
and a point `g ∈ G(U)` that conjugates the image of `i_U` onto the image of `j_U` on every
test scheme over `U`. -/
def RelativeParabolicEtaleLocalConjugacyStatement : Prop :=
  ∀ (S : Scheme.{u}) (G P Q : GroupScheme S) (i : P ⟶ G) (j : Q ⟶ G) (s : S),
    IsReductive G → IsRelativeParabolicSubgroup i → IsRelativeParabolicSubgroup j →
    (∃ g : Over.mk (𝟙 (Spec (CommRingCat.of (S.residueField s)))) ⟶
        ((GroupScheme.baseChange (S.fromSpecResidueField s :
          Spec (CommRingCat.of (S.residueField s)) ⟶ S)).obj G).X,
      SubgroupFunctor.range (RelativeLevi.residueFiberHom i s ≫
          (((GroupScheme.baseChange (S.fromSpecResidueField s :
            Spec (CommRingCat.of (S.residueField s)) ⟶ S)).obj G).innerIso g).hom) =
        SubgroupFunctor.range (RelativeLevi.residueFiberHom j s)) →
    ∃ (U : Scheme.{u}) (f : U ⟶ S), Etale f ∧ (∃ x : U, f.base x = s) ∧
      ∃ g : Over.mk (𝟙 U) ⟶ ((GroupScheme.baseChange f).obj G).X,
        SubgroupFunctor.range ((GroupScheme.baseChange f).map i ≫
            (((GroupScheme.baseChange f).obj G).innerIso g).hom) =
          SubgroupFunctor.range ((GroupScheme.baseChange f).map j)

end Langlands.GroupScheme
