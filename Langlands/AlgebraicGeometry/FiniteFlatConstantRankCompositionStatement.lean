import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Constant native rank under finite flat composition -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Finite flat morphisms of constant native ranks `r` and `s` have composite
of constant native rank `r * s` over a locally noetherian target. -/
def FiniteFlatConstantRankCompositionStatement : Prop :=
  ∀ (X Y Z : Scheme.{u}) [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (q : Y ⟶ Z)
    [IsFinite f] [Flat f] [IsFinite q] [Flat q]
    (r s : ℕ),
    (∀ y : Y, f.finrank y = r) →
    (∀ z : Z, q.finrank z = s) →
    ∀ z : Z, (f ≫ q).finrank z = r * s

end Langlands.AlgebraicGeometry
