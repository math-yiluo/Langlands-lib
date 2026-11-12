import Langlands.Representation.Classification.MoeglinWaldspurgerRealization
import Langlands.Representation.Aubert.SupportSign

/-! # Unproved actual Aubert-correctness target for the MW recursion -/

noncomputable section

namespace Langlands.MoeglinWaldspurger

universe uF uV

variable {p : ℕ} [Fact p.Prime]

/-- Actual Langlands heads of the realized input and MW output, in the same GL
rank, have classes exchanged by the actual support-adjusted Aubert operator.
This proposition is a target, not a theorem. -/
def AubertCorrectness (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ρ : T.CuspidalDatum.{uV, uF}) (x : ℝ) (a : Multisegment) (n : ℕ)
    (π πdual : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : (realize ρ x a).IsLanglandsHead π)
    (hπdual : (realize ρ x (dual a)).IsLanglandsHead πdual),
    Aubert.adjustedOperator.{uF, uV} F T n
        (GeneralLinear.finiteLengthClass n F.Carrier π
          (SmoothRep.hasFiniteLength_of_isIrreducible (langlandsHead_isIrreducible hπ))) =
      GeneralLinear.finiteLengthClass n F.Carrier πdual
        (SmoothRep.hasFiniteLength_of_isIrreducible (langlandsHead_isIrreducible hπdual))

/-- All primes, actual p-adic fields and topological data, with independent field
and cuspidal-carrier universes. Unproved. -/
def UniversalAubertCorrectness : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    AubertCorrectness.{uF, uV} F T

end Langlands.MoeglinWaldspurger
