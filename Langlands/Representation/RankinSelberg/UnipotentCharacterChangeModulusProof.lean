import Langlands.Representation.RankinSelberg.UnipotentCharacterChangeModulusStatement
import Langlands.Representation.RankinSelberg.CharacterChangeSingletonBlocks
import Langlands.Group.GL.BlockModulusHaarProof

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.RankinSelberg

open GeneralLinear GeneralLinear.BlockShape Whittaker

universe uF

/-- Character-change conjugation scales the integral-normalized upper-unipotent
Haar measure by the inverse character-change modulus. -/
theorem unipotentCharacterChangeModulus :
    UnipotentCharacterChangeModulusStatement.{uF} := by
  intro p hp F T n a
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let B := singletons (n + 1)
  let := borel (B.unipotentRadical F.Carrier)
  let : BorelSpace (B.unipotentRadical F.Carrier) := ⟨rfl⟩
  let := T.unipotentRadicalTopologicalGroup B
  let e := upperUnipotentContinuousEquivRadical (n := n + 1) F.Carrier
  let μ := unipotentHaar F.Carrier n
  have he : Measurable e := e.continuous.measurable
  have hC := measurable_characterChangeConj a n
  have hL : Measurable (B.leviAction F.Carrier (characterChangeLevi a n)) :=
    ((B.continuous_leviAction F.Carrier).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hintertwine : e ∘ characterChangeConj a n =
      B.leviAction F.Carrier (characterChangeLevi a n) ∘ e := by
    funext u
    exact upperUnipotentEquivRadical_characterChangeConj a n u
  have hblock := glBlockModulusHaar p F T (n + 1) B (μ.map e)
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

end Langlands.RankinSelberg
