import Langlands.Analysis.Local.QuotientMeasure
import Mathlib.GroupTheory.DoubleCoset

/-! # The labelled Cartan series with bounded multiplicity -/

universe u

open MeasureTheory
open scoped ENNReal

namespace Langlands.HarishChandraSchwartz

open QuotientIntegration

/-- For a coarser disjoint Cartan family, refining by two finite families of
compact representatives bounds the labelled series by the square of the
number of representatives, with a lower bound whenever the cells cover. -/
def CartanLabelledSeriesStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (C : Subgroup G), C ≤ Subgroup.center G →
    ∀ (K₀ : Subgroup G) (K : OpenSubgroup G), K.toSubgroup ≤ K₀ →
    ∀ (P F S : Set G) [Countable F] [Countable S],
      S ⊆ P →
      (∀ z ∈ P, ∀ c ∈ C, z * c ∈ P) →
      Set.InjOn (leftQuotientMap C) S →
      (∀ f ∈ F, ∀ f' ∈ F, ∀ z ∈ P, ∀ z' ∈ P,
        DoubleCoset.doubleCoset (z * f) K₀ K₀ =
          DoubleCoset.doubleCoset (z' * f') K₀ K₀ → f = f' ∧ z = z') →
      ∀ (r : ℕ) (k : Fin r → G), (∀ i, k i ∈ K₀) →
        let coarse (t : F × S) :=
          leftQuotientMap C '' DoubleCoset.doubleCoset (t.2.val * t.1.val) K₀ K₀
        let cell (p : Fin r × Fin r) (t : F × S) :=
          leftQuotientMap C '' DoubleCoset.doubleCoset
            (k p.1 * (t.2.val * t.1.val) * k p.2) K K
        Pairwise (fun t t' => Disjoint (coarse t) (coarse t')) ∧
        ∀ [MeasurableSpace (LeftQuotient C)] [BorelSpace (LeftQuotient C)]
          (μ : Measure (LeftQuotient C)) (a : LeftQuotient C → ℝ≥0∞),
          let total := ∫⁻ x, a x ∂μ
          let series := ∑' p : Fin r × Fin r, ∑' t : F × S, ∫⁻ x in cell p t, a x ∂μ
          series ≤ (r : ℝ≥0∞) ^ 2 * total ∧
            ((⋃ p, ⋃ t, cell p t) = Set.univ → total ≤ series)

end Langlands.HarishChandraSchwartz
