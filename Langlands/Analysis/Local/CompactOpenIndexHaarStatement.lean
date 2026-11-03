import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Haar characters from relative compact-open indices -/

namespace Langlands.Haar

open MeasureTheory
open scoped NNReal

universe u

/-- A continuous automorphism is measured by the relative indices of an open
subgroup and its image inside one compact open subgroup. -/
def CompactOpenIndexHaarStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (α : G ≃ₜ* G) (K J : Subgroup G),
    IsCompact (K : Set G) → IsOpen (K : Set G) → IsOpen (J : Set G) →
    J ≤ K → J.map α.toMonoidHom ≤ K →
      mulEquivHaarChar α * ((J.map α.toMonoidHom).relIndex K : ℝ≥0) =
          (J.relIndex K : ℝ≥0) ∧
        (mulEquivHaarChar α = 1 ↔
          (J.map α.toMonoidHom).relIndex K = J.relIndex K)

end Langlands.Haar
