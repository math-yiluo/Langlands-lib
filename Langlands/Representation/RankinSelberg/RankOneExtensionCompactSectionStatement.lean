import Langlands.Representation.RankinSelberg.RankOneExtensionAnalyticData

/-!
# Normalized compact sections for the strict rank-one extension

JPSS (1983), Lemma (5.5), printed 424–425, formulas (5)–(7): an actual section of
the lower induction of `(σ, χ)`, supported in the lower opposite parabolic times the
complementary upper cell, whose restriction to that cell is a normalized compact test
function times a fixed pure tensor, with the test function supported where the
supplied vector of `π` is fixed. This module only defines the proposition.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis GeneralLinear

universe uF uV uW

/-- The normalized compact-section construction of the early JPSS Lemma (5.5)
argument, in the strict rank range `t + 3 ≤ r + 1` with `r + 1 = (1 + (t + 1)) + (k + 1)`.
For every open neighbourhood `O` of zero in the row space `Fin (t + 1) → F`, there are a
Schwartz–Bruhat function `φ` supported in `O` with integral one for the supplied
self-dual row measure, and an actual section `f` of the published lower induction of
`(σ, χ)` such that `f (u(y)) = φ y • (w ⊗ 1)` on the upper cell, `f` vanishes off
`P̄ · u(supp φ)`, and every `y ∈ supp φ` fixes `v` under `π (diag(u(y), I_(k+1)))`. -/
def RankOneExtensionCompactSectionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (t k : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear ((1 + (t + 1)) + (k + 1)) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)
    (v : V) (w : W),
    (letI := F.canonicalTopologicalData.topology; IsSmooth π) →
    (letI := F.canonicalTopologicalData.topology; IsSmooth σ) →
    letI := F.canonicalTopologicalData.topology
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ O : Set (Fin (t + 1) → F.Carrier), IsOpen O → (0 : Fin (t + 1) → F.Carrier) ∈ O →
      ∃ (φ : SchwartzBruhat (Fin (t + 1) → F.Carrier))
        (f : rankOneExtensionLowerSection F t χ σ),
        Function.support φ ⊆ O ∧
        Integrable φ (rowMeasure ν.val (t + 1)) ∧
        ∫ y, φ y ∂rowMeasure ν.val (t + 1) = 1 ∧
        (∀ y : Fin (t + 1) → F.Carrier,
          rankOneExtensionLowerSectionEval F t χ σ f (rankOneExtensionUpperCell t y) =
            φ y • rankOneExtensionLowerPureTensor w (ULift.up 1)) ∧
        (∀ g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier,
          rankOneExtensionLowerSectionEval F t χ σ f g ≠ 0 →
            ∃ q : (rankOneExtensionLowerShape t).oppositeParabolic F.Carrier,
              ∃ y ∈ Function.support φ,
                g = (q : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier) *
                  rankOneExtensionUpperCell t y) ∧
        (∀ y ∈ Function.support φ,
          π (rankInclusion (k + 1) (rankOneExtensionUpperCell t y)) v = v)

end Langlands.RankinSelberg
