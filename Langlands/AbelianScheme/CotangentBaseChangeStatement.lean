import Langlands.AbelianScheme.LieBaseChange

/-! # Cotangent base-change isomorphism target -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The canonical cotangent comparison is invertible for every base change. -/
def CotangentBaseChangeIsIsoStatement (S : AlgebraicGeometry.Scheme.{u}) : Prop :=
  ∀ (T : AlgebraicGeometry.Scheme.{u}) (b : T ⟶ S) (G : GroupScheme S),
    IsIso (cotangentBaseChangeMap b G)

end Langlands.GroupScheme
