import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteSurjectiveFiniteAffineNeighborhoodsDescentStatement
import Mathlib.AlgebraicGeometry.QuasiAffine

/-! # AF representability from a finite surjection with quasi-affine source

A specialization of Gross, Proposition 3.5, to a finite surjection and a
quasi-affine source over an affine base. The conclusion is an AF scheme.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A finite surjective image of a quasi-affine scheme is represented by an AF scheme. -/
def FiniteSurjectiveQuasiAffineSourceAFStatement : Prop :=
  ∀ (R : Type u) [CommRing R]
    (U : Over (Spec (CommRingCat.of R)))
    (Y : AlgebraicSpace (Spec (CommRingCat.of R)))
    (f : (schemeToSpace _).obj U ⟶ Y),
    IsQuasiCompact Y →
      IsQuasiSeparated Y →
        U.left.IsQuasiAffine →
          IsFinite (hom f) →
            IsSurjective (hom f) →
              ∃ P : Over (Spec (CommRingCat.of R)),
                PointTopology.HasFiniteAffineNeighborhoods P.left ∧
                  Nonempty ((schemeYoneda _).obj P ≅ Y.presheaf)

end Langlands.AlgebraicGeometry.AlgebraicSpace
