import Langlands.GroupScheme.Rational.LeviSubgroup

/-! # Geometric solvable radicals of connected reductive groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every connected reductive group over a field has a represented solvable
radical that remains the solvable radical over the algebraic closure. -/
def ReductiveGeometricSolvableRadicalExistsStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
      ∃ (R : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ G),
        IsGeometricSolvableRadical r

end Langlands.GroupScheme
