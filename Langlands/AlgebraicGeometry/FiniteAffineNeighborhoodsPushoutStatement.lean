import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionRepresentability
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Finite-set affine neighborhoods of a finite-map scheme pushout -/

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry

/-- The AF-preservation consequence of Ferrand's Theorem 5.4, expressed for
an arbitrary actual scheme pushout of the given span. -/
def FiniteAffineNeighborhoodsPushoutStatement : Prop :=
  ∀ (X Y Z P : Scheme.{u}) (i : Z ⟶ X) (j : Z ⟶ Y)
    (a : X ⟶ P) (b : Y ⟶ P),
    IsClosedImmersion i →
      IsFinite j →
        PointTopology.HasFiniteAffineNeighborhoods X →
          PointTopology.HasFiniteAffineNeighborhoods Y →
            IsPushout i j a b →
              PointTopology.HasFiniteAffineNeighborhoods P

end Langlands.AlgebraicGeometry
