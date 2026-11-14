import Langlands.Representation.RankinSelberg.UnipotentCharacterChangeModulusProof
import Langlands.AllField.Group.GL.BlockModulusHaarProof
import Langlands.AllField.Representation.RankinSelberg.CharacterChangeSingletonBlocks
import Langlands.AllField.Representation.RankinSelberg.UnipotentCharacterChangeModulusStatement
noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnipotentCharacterChangeModulusStatement leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow normalizedAbsoluteValue normalizedAbsoluteValue_apply unipotentCharacterChangeModulus
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.GeneralLinear.BlockShape
open Langlands.Whittaker

universe uF

/-- Character-change conjugation scales the integral-normalized upper-unipotent
Haar measure by the inverse character-change modulus. -/
theorem unipotentCharacterChangeModulus :
    UnipotentCharacterChangeModulusStatement.{uF} := by
  intro F _ T n a
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let B := singletons (n + 1)
  let := borel (B.unipotentRadical F)
  let : BorelSpace (B.unipotentRadical F) := ⟨rfl⟩
  let := T.unipotentRadicalTopologicalGroup B
  let e := upperUnipotentContinuousEquivRadical (n := n + 1) F
  let μ := unipotentHaar F n
  have he : Measurable e := e.continuous.measurable
  have hC := measurable_characterChangeConj a n
  have hL : Measurable (B.leviAction F (characterChangeLevi a n)) :=
    ((B.continuous_leviAction F).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hintertwine : e ∘ characterChangeConj a n =
      B.leviAction F (characterChangeLevi a n) ∘ e := by
    funext u
    exact upperUnipotentEquivRadical_characterChangeConj a n u
  have hblock := glBlockModulusHaar F T (n + 1) B (μ.map e)
    (characterChangeLevi a n)
  rw [leviModulus_characterChangeLevi] at hblock
  apply (show MeasurableEmbedding e from e.toHomeomorph.measurableEmbedding).map_injective
  rw [Measure.map_map he hC, hintertwine, ← Measure.map_map hL he,
    Measure.map_smul _ he.aemeasurable, hblock]
  change ((characterChangeModulus (normalizedAbsoluteValue T) a n)⁻¹ : ℝ≥0) •
      μ.map e = ((characterChangeModulus (normalizedAbsoluteValue T) a n : ℝ≥0∞)⁻¹) •
        μ.map e
  rw [← ENNReal.coe_inv (characterChangeModulus_ne_zero _ a n)]
  rfl

end Langlands.AllField.RankinSelberg
