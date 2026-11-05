import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints

/-!
# Points of separated algebraic spaces with values in product rings

For a separated algebraic space over `Spec C` and any family of `C`-algebras, a point
with values in the product algebra is determined by its images in the factors.
-/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The injectivity half of Conrad's (3.6.2) and of his Proposition 5.2, for separated
algebraic spaces: the map from points with values in `∏ R i` to the family of points
with values in the factors `R i` is injective. -/
def SeparatedProductPointsInjectiveStatement : Prop :=
  ∀ (C : Type u) [CommRing C] (X : AlgebraicSpace (Spec (CommRingCat.of C))),
    IsSeparated X →
      ∀ (ι : Type u) (R : ι → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)],
        Function.Injective
          (fun (p : RingPoints C X (∀ i, R i)) (i : ι) =>
            RingPoints.changeRing (Pi.evalAlgHom C R i) p)

end Langlands.AlgebraicGeometry.AlgebraicSpace
