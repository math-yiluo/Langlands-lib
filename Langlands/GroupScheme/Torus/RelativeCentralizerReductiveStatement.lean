import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: centralizers of tori in reductive group schemes are reductive -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Torus centralizers in reductive group schemes** (Conrad, *Reductive group schemes*
(2014), the paragraph before Remark 3.1.5, using Lemma 2.2.4). For a reductive group
scheme `G` over a scheme `S` and a closed `S`-torus `t : T ⟶ G`, the all-test centralizer
of `t` is represented by a closed subgroup scheme, and every subgroup scheme representing
it is reductive over `S`. -/
def RelativeTorusCentralizerReductiveStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) (T : CommGroupScheme S) (t : T.toGrp ⟶ G),
    IsReductive G → RelativeTorus.IsTorus T.toGrp → IsClosedSubgroup t →
      (∃ (Z : GroupScheme S) (z : Z ⟶ G),
        IsClosedSubgroup z ∧ (torusCentralizer t).IsRepresentedBy z) ∧
      ∀ (Z : GroupScheme S) (z : Z ⟶ G),
        (torusCentralizer t).IsRepresentedBy z → IsReductive Z

end Langlands.GroupScheme
