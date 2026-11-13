import Langlands.Representation.Whittaker.SmoothSimpleRootSupportStatement
import Langlands.AllField.Group.GL.Padic
namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding SmoothSimpleRootSupportStatement
open Langlands.AllField.Whittaker

open Langlands.HarmonicAnalysis

universe uF uV

/-- Uniform simple-root support for each actual smooth Whittaker coefficient.
This proposition chooses its bound before the diagonal, integral factor, and root. -/
def SmoothSimpleRootSupportStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (r : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  ∀ ψ : UnitaryAdditiveCharacter F,
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V,
      IsSmooth π →
      ∀ ℓ : glFunctionals ψ r π,
        ∀ f : (coefficientModel π ℓ).toSubmodule,
          ∃ R : ℝ, 0 < R ∧
            ∀ (a : Fin (r + 1) → Fˣ)
              (κ : Langlands.GeneralLinear (r + 1) F),
              κ ∈ Conductor.integralSubgroup
                (ValuativeRel.valuation F).integer r →
              f.val.val (GeneralLinear.Iwasawa.diagonalUnits a * κ) ≠ 0 →
              ∀ i : Fin r,
                T.normalizedAbs ((a i.castSucc / a i.succ : Fˣ) :
                  F) ≤ R

end Langlands.AllField.Whittaker
