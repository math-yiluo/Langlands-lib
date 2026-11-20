import Langlands.BruhatTits.SpecialCompact.SmallSubgroupPredicates
import Langlands.BruhatTits.SpecialCompact.ContractionPredicates
import Langlands.Group.HaarModulus
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DoubleCosetMeasure

/-! # Iwahori double-coset volume with the Levi intersection index -/

universe u

open MeasureTheory
open scoped ENNReal NNReal Pointwise

namespace Langlands.HarishChandraSchwartz

open BruhatTits.SpecialCompact

/-- The corrected set, index and Haar volume formulas of Renard VII.1.2
under the two radical contractions at an actual Levi point. -/
def IwahoriLeviDoubleCosetVolumeStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    (K : OpenSubgroup G) (M N Nbar : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (hN : IsClosed (N : Set G)) (m : M),
    IsCompact (K : Set G) →
    M ≤ Subgroup.normalizer (Nbar : Set G) →
    Function.Injective (fun t : Nbar × M × N => (t.1 : G) * (t.2.1 : G) * (t.2.2 : G)) →
    HasIwahoriIntersectionDecomposition K.toSubgroup M N Nbar →
    WeakChamberContraction K.toSubgroup N Nbar {(m : G)} →
    let KM := K.toSubgroup ⊓ M
    let KN := K.toSubgroup ⊓ N
    DoubleCoset.doubleCoset (m : G) K K =
      (KN : Set G) * (KM : Set G) * {(m : G)} * (K : Set G) ∧
    doubleCosetIndex K.toSubgroup m =
      doubleCosetIndex KM m * (conjSubgroup (m : G) KN).relIndex KN ∧
    ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure],
      μ (DoubleCoset.doubleCoset (m : G) K K) =
        (doubleCosetIndex KM m : ℝ≥0∞) *
          ENNReal.ofReal (((HaarModulus.closedRestrictCharacter N hN M hMN m : ℝ≥0) : ℝ)⁻¹) *
          μ (K : Set G)

end Langlands.HarishChandraSchwartz
