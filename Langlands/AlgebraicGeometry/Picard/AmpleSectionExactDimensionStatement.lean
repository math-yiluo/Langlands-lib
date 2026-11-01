import Langlands.AlgebraicGeometry.Picard.Ample
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Exact-dimensional ample section cuts on irreducible schemes -/

universe u

open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- A finite-dimensional compact scheme has a closed point of maximal
stalk dimension. On an irreducible locally Noetherian scheme with an ample
line bundle, a positive tensor power has a section whose nonempty vanishing
set has exactly one less dimension. -/
def AmpleSectionExactDimensionStatement : Prop :=
  (∀ (X : Scheme.{u}) [CompactSpace X] (d : ℕ),
    topologicalKrullDim X = (d : WithBot ℕ∞) →
      ∃ x : X, IsClosed ({x} : Set X) ∧
        ringKrullDim (X.presheaf.stalk x) = (d : WithBot ℕ∞)) ∧
  (∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IrreducibleSpace X]
    (d : ℕ), 0 < d → topologicalKrullDim X = (d : WithBot ℕ∞) →
      ∀ (L : LineBundle X), L.IsAmple →
        ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
          (∃ y : X, y ∈ L.sectionOpen s) ∧
          (∃ x : X, x ∉ L.sectionOpen s) ∧
          topologicalKrullDim {x : X // x ∉ L.sectionOpen s} + 1 =
            (d : WithBot ℕ∞))

end Langlands.AlgebraicGeometry.Picard
