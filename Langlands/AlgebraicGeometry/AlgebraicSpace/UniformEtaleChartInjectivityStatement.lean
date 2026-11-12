import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartLocalSeparation

/-!
# Uniform injectivity of affine étale charts over normed extensions

A finite family of regular functions on an affine étale chart separates nearby
points of the same fibre uniformly over every normed field extension, on each
bounded coordinate locus. This is a derived algebraic and analytic prerequisite
for studying rational-point topology under ground-field extension.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint ringTest AffineCoordinateRing affineSchemePointEquiv)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- An affine finite-type étale chart of a separated space admits finitely many
regular functions such that, on each bounded coordinate locus, sufficiently close
points in the same fibre coincide, with the bound uniform over all normed extensions. -/
def UniformEtaleChartInjectivityStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K]
    (X : AlgebraicSpace (Spec (CommRingCat.of K))), IsSeparated X →
    ∀ (U : Over (Spec (CommRingCat.of K))) [IsAffine U.left]
      [LocallyOfFiniteType U.hom]
      (a : (schemeYoneda _).obj U ⟶ X.presheaf), IsEtale a →
      ∃ (n : ℕ) (f : Fin n → AffineCoordinateRing K U),
        ∀ R : ℝ, 0 < R → ∃ δ : ℝ, 0 < δ ∧
          ∀ (L : Type u) [NontriviallyNormedField L] [NormedAlgebra K L]
            (p q : RingPoint K U L),
            (∀ i, ‖affineSchemePointEquiv K U L p (f i)‖ ≤ R) →
            (∀ i, ‖affineSchemePointEquiv K U L q (f i)‖ ≤ R) →
            (∀ i, ‖affineSchemePointEquiv K U L p (f i) -
              affineSchemePointEquiv K U L q (f i)‖ < δ) →
            a.app (op (ringTest K L)) (ULift.up p) =
              a.app (op (ringTest K L)) (ULift.up q) → p = q

end Langlands.AlgebraicGeometry.AlgebraicSpace
