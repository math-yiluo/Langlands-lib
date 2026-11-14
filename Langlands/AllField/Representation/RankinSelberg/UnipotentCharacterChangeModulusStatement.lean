import Langlands.Representation.RankinSelberg.UnipotentCharacterChangeModulusStatement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement
/-!
# Unipotent Haar measure under character-change conjugation

Conjugation by `d_a = diag(a^n, ..., a, 1)` scales the coordinate `(i,j)` of the
upper-unipotent group by `a^(j-i)`. The proposition below states that the actual
integral-normalized unipotent Haar measure is pushed forward to the reciprocal
modulus times itself. It does not prove that law. The two helper theorems only
show that the pushforward is along a continuous, hence Borel measurable, map.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnipotentCharacterChangeModulusStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.Whittaker

universe uF

section Helpers


end Helpers

/-- For every p-adic field with its supplied topological data, every rank `n + 1`
and every unit `a`, conjugation `u ↦ d_a u d_a⁻¹` pushes the integral-normalized
unipotent Haar measure forward to `|a|^(-E)` times itself, where
`E = characterChangeRootExponent n` and `|·|` is the normalized absolute value. -/
def UnipotentCharacterChangeModulusStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F)
    (n : ℕ) (a : Fˣ),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (upperUnipotent (n + 1) F)
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    Measure.map (characterChangeConj a n) (unipotentHaar F n) =
      ((characterChangeModulus (normalizedAbsoluteValue T) a n : ENNReal)⁻¹) •
        unipotentHaar F n

end Langlands.AllField.RankinSelberg
