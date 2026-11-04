import Langlands.GroupScheme.Rational.LeviSubgroup

/-! # The centralizer Levi of a maximal torus of a parabolic radical -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The ambient whole-torus centralizer of a maximal torus of a supplied
geometric solvable radical of a rational parabolic is an actual rational Levi. -/
def ParabolicRadicalTorusCentralizerLeviStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
      IsParabolicSubgroup j →
      ∀ (R : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ P),
        IsGeometricSolvableRadical r →
        ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (sR : S.toGrp ⟶ R),
          IsMaximalTorus sR →
          ∃ (L : GroupScheme (Spec (CommRingCat.of k))) (l : L ⟶ P),
            IsRationalLeviSubgroup l ∧
              (torusCentralizer (sR ≫ r ≫ j)).IsRepresentedBy (l ≫ j)

end Langlands.GroupScheme
