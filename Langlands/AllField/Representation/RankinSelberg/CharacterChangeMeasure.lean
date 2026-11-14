import Langlands.Representation.RankinSelberg.CharacterChangeMeasure
import Langlands.AllField.Representation.RankinSelberg.CharacterChangeMeasureStatement
import Langlands.AllField.Representation.RankinSelberg.UnipotentCharacterChangeModulusProof
/-!
# The character-change quotient Haar law from the subgroup modulus

If conjugation by `d_a` pushes unipotent Haar measure forward to `c⁻¹` times
itself, then left translation by `d_a` pushes every compatible quotient measure
forward to `c` times itself. The proof shows that `c⁻¹` times the pushforward
is again compatible and applies quotient-measure uniqueness. The reduction is
then specialized to the canonical p-adic statement, and the published subgroup
law `unipotentCharacterChangeModulus` discharges its hypothesis.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding CharacterChangeCompatibleMeasureStatement EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnipotentCharacterChangeModulusStatement characterChangeCompatibleMeasure characterChangeCompatibleMeasure_of_unipotentModulus leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow normalizedAbsoluteValue normalizedAbsoluteValue_apply unipotentCharacterChangeModulus
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory MeasureTheory.Measure
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.Whittaker
open scoped NNReal ENNReal

universe uF

section Conditional





end Conditional

/-- The subgroup modulus statement implies the canonical quotient law. -/
theorem characterChangeCompatibleMeasure_of_unipotentModulus
    (hN : UnipotentCharacterChangeModulusStatement.{uF}) :
    CharacterChangeCompatibleMeasureStatement.{uF} := by
  intro F _ T n a
  let _ := T.topology
  let _ := T.valuativeRel
  let _ := T.localField
  let _ := borel (Langlands.GeneralLinear (n + 1) F)
  let _ : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let _ := borel (upperUnipotent (n + 1) F)
  let _ : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let _ := borel (LeftUnipotentQuotient n F)
  let _ : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  exact fun μ hμ => hasCharacterChangeMeasureLaw_of_unipotentModulus n
    (normalizedAbsoluteValue T) a (hN F T n a) μ hμ

/-- Left translation by `d_a` multiplies every compatible quotient measure by the
canonical character-change modulus. -/
theorem characterChangeCompatibleMeasure :
    CharacterChangeCompatibleMeasureStatement.{uF} :=
  characterChangeCompatibleMeasure_of_unipotentModulus unipotentCharacterChangeModulus

end Langlands.AllField.RankinSelberg
