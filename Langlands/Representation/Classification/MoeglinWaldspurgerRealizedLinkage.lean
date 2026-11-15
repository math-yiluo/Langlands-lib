import Langlands.Representation.Classification.MoeglinWaldspurgerRealization
import Langlands.Representation.Classification.SegmentIntervalLinkage
import Langlands.Representation.Classification.SegmentLinkageOrientationProof
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof

/-!
# Precedence and linkage of realized integer intervals

On one cuspidal line `ν^{x+ℤ} ρ`, precedence and linkage of the realized segments are the
usual endpoint conditions on integer intervals.
-/

noncomputable section

namespace Langlands.MoeglinWaldspurger.Derivation

open Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}
  (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ)

theorem realize_hasIntegralCoordinates (I : Interval) :
    (I.realize ρ x).HasIntegralCoordinates (ρ.twist x) I.beginning I.ending := by
  refine ⟨?_, ?_⟩
  · rw [Interval.realize_base, CuspidalDatum.twist_twist, add_comm]
  · rw [Interval.realize_length]
    unfold Interval.length
    have := Int.toNat_of_nonneg (sub_nonneg.mpr I.nonempty)
    push_cast
    omega

variable (F T) in
/-- Precedence of realized intervals is the endpoint configuration `a < c ≤ b + 1, b < d`. -/
theorem realize_precedes_iff (I J : Interval) :
    (I.realize ρ x).Precedes (J.realize ρ x) ↔
      I.beginning < J.beginning ∧ J.beginning ≤ I.ending + 1 ∧ I.ending < J.ending :=
  (realize_hasIntegralCoordinates ρ x I).precedes_iff
    (Classification.cuspidalIntegralTwistFreeness.{uF, uV} F T)
    (realize_hasIntegralCoordinates ρ x J)

variable (F T) in
/-- Linkage of realized intervals: one precedes the other. -/
theorem realize_isLinked_iff (I J : Interval) :
    (I.realize ρ x).IsLinked (J.realize ρ x) ↔
      (I.beginning < J.beginning ∧ J.beginning ≤ I.ending + 1 ∧ I.ending < J.ending) ∨
        (J.beginning < I.beginning ∧ I.beginning ≤ J.ending + 1 ∧ J.ending < I.ending) := by
  rw [← realize_precedes_iff F T ρ x I J, ← realize_precedes_iff F T ρ x J I]
  constructor
  · exact fun h => h.precedes_or_precedes
  · rintro (h | h)
    · exact h.isLinked
    · exact h.isLinked.symm

end Langlands.MoeglinWaldspurger.Derivation
