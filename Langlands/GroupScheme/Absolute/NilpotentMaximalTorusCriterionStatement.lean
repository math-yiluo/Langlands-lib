import Langlands.GroupScheme.Nilpotent.Basic
import Langlands.GroupScheme.Rational.Characters
import Mathlib.Data.List.TFAE

/-! # Statement: nilpotence criteria through maximal tori and Borel subgroups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Proposition 17.23. For a smooth connected affine group `G` over an
algebraically closed field the following are equivalent:
(a) any two maximal tori of `G` have the same all-test points;
(b) some Borel subgroup of `G` is nilpotent;
(c) `G` is nilpotent;
(d) every maximal torus of `G` is central. -/
def NilpotentMaximalTorusCriterionStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    List.TFAE
      [∀ (T T' : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G)
          (j' : T'.toGrp ⟶ G), IsMaximalTorus j → IsMaximalTorus j' →
            SubgroupFunctor.range j = SubgroupFunctor.range j',
        ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G),
          IsBorelSubgroup i ∧ IsNilpotentGroupScheme B,
        IsNilpotentGroupScheme G,
        ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
          IsMaximalTorus j → IsCentral j]

end Langlands.GroupScheme
