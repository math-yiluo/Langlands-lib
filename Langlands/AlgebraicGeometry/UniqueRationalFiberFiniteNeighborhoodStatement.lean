import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # A unique rational fiber of a proper map has a finite neighborhood -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Uniqueness of a rational fiber gives a singleton topological fiber and
a target neighborhood over which the whole proper morphism is finite. -/
def UniqueRationalFiberFiniteNeighborhoodStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (X Y : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of K)) (q : Y ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType p] [LocallyOfFiniteType q]
    (f : X ⟶ Y) [IsProper f],
    f ≫ q = p →
    ∀ (x : Spec (CommRingCat.of K) ⟶ X), Picard.IsRationalPoint p x →
      (∀ (x' : Spec (CommRingCat.of K) ⟶ X), Picard.IsRationalPoint p x' →
        x' ≫ f = x ≫ f → x' = x) →
      (f ⁻¹' {f (x (IsLocalRing.closedPoint K))} =
        {x (IsLocalRing.closedPoint K)}) ∧
      ∃ V : Y.Opens,
        f (x (IsLocalRing.closedPoint K)) ∈ V ∧ IsFinite (f ∣_ V)

end Langlands.AlgebraicGeometry
