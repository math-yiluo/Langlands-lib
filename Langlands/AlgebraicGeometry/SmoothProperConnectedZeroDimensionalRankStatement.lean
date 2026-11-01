import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Native endomorphism rank in relative dimension zero -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A smooth proper geometrically connected zero-dimensional scheme over an
algebraically closed field is the base scheme. Its actual over-endomorphisms
are identities and have native rank one. -/
def SmoothProperConnectedZeroDimensionalRankStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (X : Over (Spec (CommRingCat.of K))),
    SmoothOfRelativeDimension 0 X.hom →
      IsProper X.hom → GeometricallyConnected X.hom →
        IsIso X.hom ∧
          ∀ (f : X ⟶ X), f.left = 𝟙 X.left ∧
            ∀ (x : X.left), f.left.finrank x = 1

end Langlands.AlgebraicGeometry
