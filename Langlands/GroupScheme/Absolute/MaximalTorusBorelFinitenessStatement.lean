import Langlands.GroupScheme.Absolute.Borel

/-! # Statement: a maximal torus lies in finitely many Borel subgroups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Corollary 17.26(a). In a smooth connected affine group over an
algebraically closed field, a maximal torus lies in only finitely many Borel
subgroups: the all-test subgroup functors of the Borel subgroups containing it form
a finite set. -/
def MaximalTorusBorelFinitenessStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G), IsMaximalTorus j →
      Set.Finite {F : SubgroupFunctor G |
        ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G),
          IsBorelSubgroup i ∧ SubgroupFunctor.range i = F ∧ SubgroupFunctor.range j ≤ F}

end Langlands.GroupScheme
