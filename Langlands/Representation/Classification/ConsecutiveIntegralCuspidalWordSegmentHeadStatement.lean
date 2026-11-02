import Langlands.Representation.Classification.IntegralCuspidalJacquetWord
import Langlands.Representation.Classification.Segments

/-! A decreasing consecutive actual word detects the strong special head. -/

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

/-- An actual decreasing consecutive cuspidal Jacquet word identifies the
strong special head of the segment beginning at its lowest label. -/
def ConsecutiveIntegralCuspidalWordSegmentHead : Prop :=
  letI := T.topology
  ∀ (m : ℕ) (hm : 0 < m)
    (A : SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := m))
    (l : ℕ) (hl : 0 < l) (a : ℤ)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (l * m) F.Carrier)),
    π.IsIrreducible → π.IsAdmissible →
    IntegralCuspidalJacquetWord F T m (l * m) A π
      (List.ofFn (fun i : Fin l => a - (i.val : ℤ))) →
    let Δ : Segment.{max uF uV, uF} T :=
      ⟨⟨m, hm, T.supercuspidalClassRealPowerTwist m
        ((a - ((l - 1 : ℕ) : ℤ) : ℤ) : ℝ) A.isoClass⟩, l, hl⟩
    T.IsSegmentHead Δ π

end Langlands.Classification
