import Langlands.GroupScheme.Nilpotent.Basic
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Rational.TorusNormalizer

/-! # Statement: the identity component of a maximal-torus centralizer -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Proposition 17.28. Let `j : T ⟶ G` be a maximal torus of a smooth
connected affine group over an algebraically closed field, and let `c : C ⟶ G` be
a connected closed subgroup inside the centralizer of `T` that contains every
connected closed subgroup inside that centralizer, so that `c` presents
`C_G(T)°`. Then `C` is smooth and nilpotent, and every connected closed subgroup
normalizing `C` lies in `C`; that is, `C` is the identity component of its
normalizer. -/
def TorusCentralizerNormalizerStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G), IsMaximalTorus j →
    ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ G),
      IsClosedSubgroup c → ConnectedSpace C.X.left →
      SubgroupFunctor.range c ≤ torusCentralizer j →
      (∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
        IsClosedSubgroup h → ConnectedSpace H.X.left →
          SubgroupFunctor.range h ≤ torusCentralizer j →
            SubgroupFunctor.range h ≤ SubgroupFunctor.range c) →
      Smooth C.X.hom ∧ IsNilpotentGroupScheme C ∧
        ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
          IsClosedSubgroup h → ConnectedSpace H.X.left →
            SubgroupFunctor.range h ≤ (SubgroupFunctor.range c).normalizer →
              SubgroupFunctor.range h ≤ SubgroupFunctor.range c

end Langlands.GroupScheme
