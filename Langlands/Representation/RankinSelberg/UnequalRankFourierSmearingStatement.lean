import Langlands.LocalField.Definitions
import Langlands.HarmonicAnalysis.RowFourier
import Langlands.Representation.RankinSelberg.QuotientIntegrals
import Langlands.Representation.RankinSelberg.UnequalRankSmearingUnipotent

/-!
# Global and pointwise JPSS Fourier smearing in one coefficient model

This proposition retains the global right-translation integral and the
pointwise last-row cutoff for a single coefficient in the original model.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- A supplied plus-sign Fourier pair produces one coefficient in the same
model, with a genuine integral formula on the whole group and the pointwise
JPSS cutoff on every unequal-rank block. This is a statement, not a proof. -/
def UnequalRankFourierSmearingStatement (n j k : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier),
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ π : Representation ℂ
      (Langlands.GeneralLinear (n + ((j + 1) + k + 1) + 1) F.Carrier) V,
      IsSmooth π →
      ∀ (ℓ : glFunctionals ψ (n + ((j + 1) + k + 1)) π)
        (f : (coefficientModel π ℓ).toSubmodule)
        (κ Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
        IsRowFourierPair ψ ν κ Φ →
        ∃ f₁ : (coefficientModel π ℓ).toSubmodule,
          (∀ h : Langlands.GeneralLinear (n + ((j + 1) + k + 1) + 1) F.Carrier,
            Integrable
              (fun z => κ z * f.val.val (h * unequalRankSmearingUnipotent n j k z))
              (rowMeasure ν (n + 1)) ∧
            f₁.val.val h =
              ∫ z, κ z * f.val.val (h * unequalRankSmearingUnipotent n j k z)
                ∂rowMeasure ν (n + 1)) ∧
          ∀ (g : Langlands.GeneralLinear (n + 1) F.Carrier)
            (X : Matrix (Fin (j + 1)) (Fin (n + 1)) F.Carrier),
            f₁.val.val (unequalRankMatrix (j + 1) k g X) =
              Φ (X (Fin.last j)) * f.val.val (unequalRankMatrix (j + 1) k g X)

end Langlands.RankinSelberg
