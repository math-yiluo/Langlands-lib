import Langlands.Representation.Classification.MoeglinWaldspurgerAubertStatement
import Langlands.Representation.Aubert.LanglandsHeadDuality
import Langlands.Representation.Classification.SegmentUniverseLift

/-!
# From label correctness to actual Aubert correctness of the MW recursion

If every Langlands head of a realized integer multisegment is a weak Zelevinsky label of
the realized MW output, then the actual support-adjusted Aubert operator exchanges the
heads of `a` and `dual a`.
-/

noncomputable section

namespace Langlands.MoeglinWaldspurger

open PadicField.TopologicalData Aubert Aubert.SegmentPolynomialSurjectivity
open Aubert.LanglandsHeadDuality

universe uF uV

variable {p : ℕ} [Fact p.Prime]

/-- Every actual Langlands head of `realize ρ x a`, for a cuspidal datum in the saturated
carrier universe, is a weak Zelevinsky label of `realize ρ x (dual a)`. -/
def LabelCorrectness (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ρ : T.CuspidalDatum.{max uF uV, uF}) (x : ℝ) (a : Multisegment) (n : ℕ)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) (hπ : π.IsIrreducible),
    (realize ρ x a).IsLanglandsHead π →
      IsLabel.{uF, uV} F T (realize ρ x (dual a)) n
        (GeneralLinear.irreducibleIsoClass n F.Carrier π hπ)

section Lift

variable {F : PadicField.{uF} p} {T : F.TopologicalData}

theorem Interval.realize_universeLift (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ) (I : Interval) :
    (I.realize ρ x).universeLift = I.realize ρ.universeLift x := by
  change (⟨(ρ.twist (x + (I.beginning : ℝ))).universeLift, I.length, I.length_pos⟩ :
      T.Segment.{max uF uV, uF}) =
    ⟨ρ.universeLift.twist (x + (I.beginning : ℝ)), I.length, I.length_pos⟩
  rw [CuspidalDatum.universeLift_twist]

theorem realize_universeLift (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ) (a : Multisegment) :
    (realize ρ x a).universeLift = realize ρ.universeLift x a := by
  simp only [Multisegment.universeLift, realize, Multiset.map_map]
  congr 1
  funext I
  exact Interval.realize_universeLift ρ x I

end Lift

/-- Label correctness implies the published actual Aubert-correctness target. -/
theorem aubertCorrectness_of_labelCorrectness (F : PadicField.{uF} p) (T : F.TopologicalData)
    (h : LabelCorrectness.{uF, uV} F T) : AubertCorrectness.{uF, uV} F T := by
  let := T.topology
  intro ρ x a n π πdual hπ hπdual
  have hx := Aubert.binaryProductExactness.{uF, uV} F T
  have hl := Aubert.gradedInductionRingLaws F T hx
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T
  have hπirr := langlandsHead_isIrreducible hπ
  have hπdualirr := langlandsHead_isIrreducible hπdual
  have hπ' : (realize ρ.universeLift x a).IsLanglandsHead π := by
    rw [← realize_universeLift]
    exact (Multisegment.isLanglandsHead_universeLift_iff _ π).mpr hπ
  have hπdual' : (realize ρ.universeLift x (dual a)).IsLanglandsHead πdual := by
    rw [← realize_universeLift]
    exact (Multisegment.isLanglandsHead_universeLift_iff _ πdual).mpr hπdual
  have hlabel := h ρ.universeLift x a n π hπirr hπ'
  have hP := gradedAdjustedOperator_label F T hx hl ψ (realize ρ.universeLift x (dual a)) n
    _ hlabel πdual hπdualirr hπdual'
  rw [basisClass_irreducibleIsoClass, basisClass_irreducibleIsoClass,
    gradedAdjustedOperator_homogeneous] at hP
  exact DirectSum.of_injective (β := fun k =>
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} k F.Carrier) n hP

/-- The published universal target, from label correctness at every field. -/
theorem universalAubertCorrectness_of_labelCorrectness
    (h : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
      LabelCorrectness.{uF, uV} F T) :
    UniversalAubertCorrectness.{uF, uV} :=
  fun p _ F T => aubertCorrectness_of_labelCorrectness F T (h p F T)

end Langlands.MoeglinWaldspurger
