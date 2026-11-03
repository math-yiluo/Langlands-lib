import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Rational.MinimalParabolic
import Langlands.GroupScheme.Rational.SplitTorus

/-! # Rational Levis of a minimal parabolic as split-torus centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every rational Levi of a minimal rational parabolic is the whole-torus
centralizer of an ambient maximal split torus contained in its solvable radical. -/
def MinimalParabolicLeviCentralizerStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
      IsMinimalParabolicSubgroup j →
      ∀ (L : GroupScheme (Spec (CommRingCat.of k))) (l : L ⟶ P),
        IsRationalLeviSubgroup l →
        ∀ (R : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ P),
          IsGeometricSolvableRadical r →
          ∃ (B : CommGroupScheme (Spec (CommRingCat.of k))) (bR : B.toGrp ⟶ R),
            IsMaximalSplitTorus (bR ≫ r ≫ j) ∧
              torusCentralizer (bR ≫ r ≫ j) = SubgroupFunctor.range (l ≫ j)

end Langlands.GroupScheme
