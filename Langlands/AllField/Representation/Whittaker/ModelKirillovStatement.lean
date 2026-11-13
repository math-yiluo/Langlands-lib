import Langlands.Representation.Whittaker.ModelKirillovStatement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatement
import Langlands.AllField.Representation.Whittaker.KirillovStatement
/-!
# Kirillov lifting into actual coefficient models

An internal conditional interface for the compact mirabolic model of JPSS
(1983), Section 2.2, printed page 386. These proposition definitions do not
prove Kirillov surjectivity.
-/

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding ModelKirillovTransferStatement
open Langlands.AllField.Whittaker

open Langlands.HarmonicAnalysis
open Langlands.GeneralLinear
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

universe uF uV

/-- The full Whittaker-type Kirillov proposition `WhittakerTypeKirillovStatement`
implies lifting of every mirabolic test function into each nonzero-functional
coefficient model, for every supplied `T : LocalFieldData F` and every representation
of Whittaker type. -/
def ModelKirillovTransferStatement : Prop :=
  Langlands.AllField.WhittakerTypeKirillovStatement.{uF, uV} →
    ∀ (F : Type uF) [Field F]
      (T : LocalFieldData F),
      letI := T.topology
      ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
        (ψ : UnitaryAdditiveCharacter F),
        IsOfWhittakerType n (standardCharacter ψ n) π →
        ∀ ℓ : glFunctionals ψ n π, ℓ.val ≠ 0 →
        ∀ φ : WhittakerFunctions ψ n, IsMirabolicTestFunction ψ n φ →
          ∃ f : (coefficientModel π ℓ).toSubmodule,
            ∀ q : Langlands.GeneralLinear (n + 1) F,
              (∀ a, q.val (Fin.last n) a = if a = Fin.last n then 1 else 0) →
              f.val.val q = φ.val q

end Langlands.AllField.Whittaker
