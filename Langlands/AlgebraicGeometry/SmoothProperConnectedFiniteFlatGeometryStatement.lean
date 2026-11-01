import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties

/-! # Geometry and native rank before the polarized degree calculation -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Smooth proper geometrically connected schemes over fields are integral of
the stated dimension. Their finite flat endomorphisms are surjective and have
constant positive native rank. This is a proposition target. -/
def SmoothProperConnectedFiniteFlatGeometryStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (X : Over (Spec (CommRingCat.of K))) (g : ℕ),
    SmoothOfRelativeDimension g X.hom →
      IsProper X.hom → GeometricallyConnected X.hom →
        ∀ (f : X ⟶ X), IsFinite f.left → Flat f.left →
          IsIntegral X.left ∧
            topologicalKrullDim X.left = (g : WithBot ℕ∞) ∧
            Surjective f.left ∧
            (∀ x y : X.left, f.left.finrank x = f.left.finrank y) ∧
            ∀ x : X.left, 0 < f.left.finrank x

end Langlands.AlgebraicGeometry
