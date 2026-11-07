import Langlands.Representation.RankinSelberg.TemperedSupercuspidalPoleBridge
import Langlands.Representation.RankinSelberg.TemperedSupercuspidalPoleRank
import Langlands.Representation.RankinSelberg.SupercuspidalEqualRankLFactorProof

/-!
# Reduction of tempered pair poles to the remaining classification and formulas

The selected block certificate supplies the partner and polynomial. The rank
argument and carrier transport give the target's exact rank and universe data.
The equal-rank supercuspidal formula is discharged by its published proof.
Tempered block exhaustion and JPSS (8.2), (8.4) remain explicit premises.
-/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis Polynomial
open TemperedSupercuspidalPoleBridge

universe uF uV uW

section SelectedBlock

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance poleReductionTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- The selected centered seed gives both rank bounds. The partner is then
realized in the independently prescribed carrier universe, with the same
polynomial and root. -/
theorem hasSupercuspidalPolePartner_of_selectedBlockPole
    {ψ : UnitaryAdditiveCharacter F.Carrier}
    {ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ}
    {k : ℕ} {τ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)}
    (h : HasSelectedBlockPole F ψ ν k τ) :
    HasSupercuspidalPolePartner.{uF, uV, uW} F ψ ν.val τ.representation := by
  obtain ⟨l, m, hm, σ, _hσ, ⟨e⟩, i, a, d, hr, π₀, hiπ₀, hsπ₀, hc,
    ρ, hiρ, hsρ, P, hP, hroot⟩ := h
  have hrank := selectedCenteredSegment_rankBounds F m hm
    (fun j => (σ j).representation) (fun j => (σ j).isSmooth)
    τ.representation ⟨e.symm⟩ i hr π₀.representation hiπ₀ hsπ₀ hc
  have hpole : HasSupercuspidalPolePartner.{uF, uV, max uF uV}
      F ψ ν.val τ.representation :=
    ⟨a, ρ, P, hiρ, hsρ, hrank.1, hrank.2, hP, hroot⟩
  exact hpole.of_equiv (Representation.Equiv.refl τ.representation)

end SelectedBlock

/-- Exact untwisted pole existence in arbitrary carrier universes, conditional
only on tempered block exhaustion and the square-integrable and tempered
product formulas. The equal-rank supercuspidal formula is already proved. -/
theorem untwistedTemperedSupercuspidalPole_of_remaining_inputs
    (exhaustion : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
      Classification.TemperedBlockExhaustion.{uF, uV} F F.canonicalTopologicalData)
    (H82 : SquareIntegrableLFactorStatement.{uF, max uF uV, max uF uV,
      max uF uV, max uF uV})
    (H84 : TemperedLFactorStatement.{uF, max uF uV, max uF uV}) :
    UntwistedTemperedSupercuspidalPoleStatement.{uF, uV, uW} := by
  intro p _ F ψ ν k τ hk hiτ htτ
  let := F.canonicalTopologicalData.topology
  cases k with
  | zero => omega
  | succ k =>
    change HasSupercuspidalPolePartner.{uF, uV, uW} F ψ ν.val τ.representation
    exact hasSupercuspidalPolePartner_of_selectedBlockPole
      (hasSelectedBlockPole_of F ψ ν (exhaustion p F)
        supercuspidalEqualRankLFactor H82 H84 k τ hiτ htτ)

/-- The remaining three mathematical inputs imply the unchanged full target,
including every real twist and the independent partner carrier universe.
This proposition does not assert those three inputs. -/
def TemperedTwistSupercuspidalPoleReductionStatement : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    Classification.TemperedBlockExhaustion.{uF, uV} F F.canonicalTopologicalData) →
  SquareIntegrableLFactorStatement.{uF, max uF uV, max uF uV,
    max uF uV, max uF uV} →
  TemperedLFactorStatement.{uF, max uF uV, max uF uV} →
  TemperedTwistSupercuspidalPoleStatement.{uF, uV, uW}

/-- Apply the published opposite-real-twist transport to the exact untwisted
certificate. All remaining classification and formula premises stay explicit. -/
theorem temperedTwistSupercuspidalPoleReduction :
    TemperedTwistSupercuspidalPoleReductionStatement.{uF, uV, uW} := by
  intro exhaustion H82 H84
  exact temperedTwistSupercuspidalPole_of_untwisted
    (untwistedTemperedSupercuspidalPole_of_remaining_inputs exhaustion H82 H84)

end Langlands.RankinSelberg
