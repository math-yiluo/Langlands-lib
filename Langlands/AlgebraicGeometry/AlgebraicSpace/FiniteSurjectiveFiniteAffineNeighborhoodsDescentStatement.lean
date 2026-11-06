import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeLocalGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralCompactness
import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionRepresentability

/-! # Finite-surjective descent of finite-set affine neighborhoods

An affine-base specialization of Gross, Theorem 1.2: a quasi-compact,
quasi-separated algebraic space admitting a finite surjection from an actual
AF scheme is represented by an actual AF scheme over the same base.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Finite-surjective AF descent for a qcqs algebraic space over an affine base. -/
def FiniteSurjectiveFiniteAffineNeighborhoodsDescentStatement : Prop :=
  ∀ (R : Type u) [CommRing R]
    (U : Over (Spec (CommRingCat.of R)))
    (Y : AlgebraicSpace (Spec (CommRingCat.of R)))
    (f : (schemeToSpace _).obj U ⟶ Y),
    IsQuasiCompact Y →
      IsQuasiSeparated Y →
        PointTopology.HasFiniteAffineNeighborhoods U.left →
          IsFinite (hom f) →
            IsSurjective (hom f) →
              ∃ P : Over (Spec (CommRingCat.of R)),
                PointTopology.HasFiniteAffineNeighborhoods P.left ∧
                  Nonempty ((schemeYoneda _).obj P ≅ Y.presheaf)

end Langlands.AlgebraicGeometry.AlgebraicSpace
