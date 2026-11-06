import Langlands.Representation.RankinSelberg.TemperedTwistSupercuspidalPoleTransport
import Langlands.Representation.RankinSelberg.SegmentPairPoleOrder
import Langlands.Representation.Smooth.SmallRealizationProof

/-!
# Carrier universes in supercuspidal pole existence

The published small-realization theorem transports a supercuspidal pole
partner to any carrier universe. Consequently the tempered pole-existence
statements can be proved in any fixed pair of carrier universes.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW uV' uW'

variable {p : ℕ} [Fact p.Prime]

/-- A positive-rank supercuspidal partner with both required rank bounds and
a certified pair L-polynomial vanishing at one. No existence is asserted. -/
def HasSupercuspidalPolePartner
    (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {k : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear k F.Carrier) V) : Prop :=
  ∃ (r : ℕ) (ρ : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uW} ℂ (Langlands.GeneralLinear (r + 1) F.Carrier)) (P : ℂ[X]),
    (letI := F.canonicalTopologicalData.topology;
      Representation.IsIrreducible ρ.representation) ∧
    (letI := F.canonicalTopologicalData.topology;
      GeneralLinear.IsSupercuspidal ρ.representation) ∧
    r + 1 ≤ k ∧
    (¬ (letI := F.canonicalTopologicalData.topology;
      GeneralLinear.IsSupercuspidal π) → r + 1 < k) ∧
    (letI := F.canonicalTopologicalData.topology;
      IsPadicRankLPolynomial F ψ ν π ρ.representation P) ∧
    P.IsRoot 1

section Transport

variable {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}
  {k : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
  {π : Representation ℂ (Langlands.GeneralLinear k F.Carrier) V}
  {π' : Representation ℂ (Langlands.GeneralLinear k F.Carrier) V'}

/-- Transport the source through an actual equivalence and realize the partner
in an independently prescribed universe, preserving its polynomial. -/
theorem HasSupercuspidalPolePartner.of_equiv
    (h : HasSupercuspidalPolePartner.{uF, uV, uW} F ψ ν π)
    (e : π.Equiv π') :
    HasSupercuspidalPolePartner.{uF, uV', uW'} F ψ ν π' := by
  let := F.canonicalTopologicalData.topology
  obtain ⟨r, ρ, P, hρ, hsρ, hr, hstrict, hP, hroot⟩ := h
  obtain ⟨ρ', hρ', ⟨f⟩⟩ :=
    padicIrreducibleSmoothSmallRealization p F F.canonicalTopologicalData (r + 1) ρ hρ
  refine ⟨r, ρ', P, hρ', GeneralLinear.isSupercuspidal_of_equiv f hsρ,
    hr, ?_, (IsPadicRankLPolynomial.congr_equiv e f).mp hP, hroot⟩
  intro hnot
  exact hstrict (fun hs => hnot (GeneralLinear.isSupercuspidal_of_equiv e hs))

/-- Existence of a pole partner depends only on the source equivalence class,
and is independent of both carrier universes. -/
theorem hasSupercuspidalPolePartner_iff_of_equiv (e : π.Equiv π') :
    HasSupercuspidalPolePartner.{uF, uV, uW} F ψ ν π ↔
      HasSupercuspidalPolePartner.{uF, uV', uW'} F ψ ν π' :=
  ⟨fun h => h.of_equiv e, fun h => h.of_equiv e.symm⟩

end Transport

/-- It suffices to prove untwisted tempered pole existence in any chosen pair
of carrier universes. Both source and partner are transported by actual
representation equivalences. -/
theorem untwistedTemperedSupercuspidalPole_of_universes
    (h : UntwistedTemperedSupercuspidalPoleStatement.{uF, uV', uW'}) :
    UntwistedTemperedSupercuspidalPoleStatement.{uF, uV, uW} := by
  intro p _ F ψ ν k τ hk hτ ht
  let := F.canonicalTopologicalData.topology
  obtain ⟨τ', hτ', ⟨e⟩⟩ :=
    padicIrreducibleSmoothSmallRealization.{uF, uV, uV'} p F
      F.canonicalTopologicalData k τ hτ
  have ht' := (F.canonicalTopologicalData.isTempered_iff_of_equiv e).mp ht
  have hpole := h p F ψ ν k τ' hk hτ' ht'
  change HasSupercuspidalPolePartner.{uF, uV', uW'} F ψ ν.val τ'.representation at hpole
  change HasSupercuspidalPolePartner.{uF, uV, uW} F ψ ν.val τ.representation
  exact hpole.of_equiv e.symm

/-- The full target is independent of its two carrier universes. The real
exponent is handled by the opposite-twist reduction. -/
theorem temperedTwistSupercuspidalPole_of_universes
    (h : TemperedTwistSupercuspidalPoleStatement.{uF, uV', uW'}) :
    TemperedTwistSupercuspidalPoleStatement.{uF, uV, uW} :=
  temperedTwistSupercuspidalPole_of_untwisted
    (untwistedTemperedSupercuspidalPole_of_universes
      (temperedTwistSupercuspidalPole_iff_untwisted.mp h))

end Langlands.RankinSelberg
