import Langlands.GroupScheme.Rational.MinimalParabolic
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Rational.TorusCentralizer

/-! # Common split tori and conjugacy inside minimal parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The intersection of two rational parabolic subgroups contains the centralizer of an
ambient maximal split torus, on every test scheme. -/
def ParabolicIntersectionCentralizerStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P P' : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G) (j' : P' ⟶ G),
      IsParabolicSubgroup j → IsParabolicSubgroup j' →
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
        IsMaximalSplitTorus i ∧
        torusCentralizer i ≤ SubgroupFunctor.range j ∧
        torusCentralizer i ≤ SubgroupFunctor.range j'

/-- Two ambient maximal split tori contained in one minimal rational parabolic are
conjugate by a rational point of that parabolic. -/
def MinimalParabolicSplitTorusConjugacyStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
      IsMinimalParabolicSubgroup j →
      ∀ (T T' : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
        (i' : T'.toGrp ⟶ G), IsMaximalSplitTorus i → IsMaximalSplitTorus i' →
        ∀ (f : T.toGrp ⟶ P) (f' : T'.toGrp ⟶ P), f ≫ j = i → f' ≫ j = i' →
          ∃ (p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X) (e : T.toGrp ≅ T'.toGrp),
            f ≫ (P.innerIso p).hom = e.hom ≫ f'

end Langlands.GroupScheme
