import Langlands.AlgebraicGeometry.ModuleLinear
import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Finitely many sections already separate points and tangent vectors -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Let `X` be a proper scheme over an algebraically closed field `K` and `L` a line bundle
whose complete linear system separates rational points and nonzero rational tangent vectors.
Then finitely many global sections `s 0, …, s n` suffice. They have no common zero at any
point of `X`, and their `K`-linear combinations `∑ i, c i • s i` separate distinct rational
points and nonzero rational tangent vectors.
This proposition is a statement target, not a proof. -/
def FiniteSeparatingSectionsStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of K)) (L : Picard.LineBundle X),
    IsProper p → Picard.SeparatesPointsAndTangents p L →
    ∃ (n : ℕ) (s : Fin (n + 1) → SchemeModule.GlobalSections L.obj),
      (∀ x : X, ∃ i, x ∈ SchemeModule.nonvanishingLocus L.obj (s i)) ∧
      (∀ x y : Spec (CommRingCat.of K) ⟶ X, Picard.IsRationalPoint p x →
        Picard.IsRationalPoint p y → x ≠ y →
        ∃ c : Fin (n + 1) → K,
          Picard.VanishesAlong L x (∑ i, Scheme.Modules.scalarsFromBase p (c i) • s i) ∧
            ¬ Picard.VanishesAlong L y (∑ i, Scheme.Modules.scalarsFromBase p (c i) • s i)) ∧
      (∀ x : Spec (CommRingCat.of K) ⟶ X, Picard.IsRationalPoint p x →
        ∀ t : Spec (CommRingCat.of (DualNumber K)) ⟶ X, Picard.IsNonzeroTangentVectorAt p x t →
        ∃ c : Fin (n + 1) → K,
          Picard.VanishesAlong L x (∑ i, Scheme.Modules.scalarsFromBase p (c i) • s i) ∧
            ¬ Picard.VanishesAlong L t (∑ i, Scheme.Modules.scalarsFromBase p (c i) • s i))

end Langlands.AlgebraicGeometry
