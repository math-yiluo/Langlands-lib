import Langlands.GroupScheme.Rational.LeviSubgroup

/-! # Geometric solvable radicals of rational parabolics -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every rational parabolic of a connected reductive group has a represented
solvable radical that remains the solvable radical over the algebraic closure. -/
def ParabolicGeometricSolvableRadicalExistsStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
      IsParabolicSubgroup j →
      ∃ (R : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ P),
        IsGeometricSolvableRadical r

end Langlands.GroupScheme
