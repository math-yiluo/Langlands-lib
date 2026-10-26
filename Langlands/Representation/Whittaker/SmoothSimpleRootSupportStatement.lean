import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Representation.Whittaker.Iwasawa
import Langlands.LocalField.Normalization.Definitions

namespace Langlands.Whittaker

open HarmonicAnalysis

universe uF uV

/-- Uniform simple-root support for each actual smooth Whittaker coefficient.
This proposition chooses its bound before the diagonal, integral factor, and root. -/
def SmoothSimpleRootSupportStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (r : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V,
      IsSmooth π →
      ∀ ℓ : glFunctionals ψ r π,
        ∀ f : (coefficientModel π ℓ).toSubmodule,
          ∃ R : ℝ, 0 < R ∧
            ∀ (a : Fin (r + 1) → F.Carrierˣ)
              (κ : Langlands.GeneralLinear (r + 1) F.Carrier),
              κ ∈ Conductor.integralSubgroup
                (ValuativeRel.valuation F.Carrier).integer r →
              f.val.val (GeneralLinear.Iwasawa.diagonalUnits a * κ) ≠ 0 →
              ∀ i : Fin r,
                T.normalizedAbs ((a i.castSucc / a i.succ : F.Carrierˣ) :
                  F.Carrier) ≤ R

end Langlands.Whittaker
