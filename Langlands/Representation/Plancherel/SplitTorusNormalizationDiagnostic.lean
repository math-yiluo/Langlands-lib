import Langlands.Representation.Plancherel.SplitTorusPositiveCharacter
import Langlands.Representation.Twist.RealPower

/-! # Absolute-value characters and the rank-one real-part normalization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped TensorProduct CategoryTheory.MonObj NNReal
open Langlands.GroupScheme

namespace Langlands.Plancherel.SplitTorus

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}

/-- The published residue-normalized absolute value of an actual algebraic character,
embedded as a complex character. -/
def normalizedAbsoluteValueCharacter (α : characterLattice A) :
    rationalPoints A.toGrp →* ℂˣ :=
  Langlands.positiveUnitsToComplex.comp
    (rationalNormCharacters A.toGrp
      ((rationalCharacters.equivCharacterLattice A).symm α)).toMul

@[simp] theorem normalizedAbsoluteValueCharacter_val (α : characterLattice A)
    (a : rationalPoints A.toGrp) :
    (normalizedAbsoluteValueCharacter α a : ℂ) =
      (LocalField.residueNormalizedAbsoluteValue F
        (rationalCharacterEval
          ((rationalCharacters.equivCharacterLattice A).symm α) a : F) : ℂ) := rfl

/-- Normalized absolute-value characters are exactly the positive characters of
their integral character parameters. -/
theorem normalizedAbsoluteValueCharacter_eq_positiveCharacter
    (hA : IsSplitTorus A.toGrp) (α : characterLattice A) :
    normalizedAbsoluteValueCharacter α =
      positiveCharacter hA ((1 : ℝ) ⊗ₜ[ℤ] α) := by
  apply MonoidHom.ext
  intro a
  apply Units.ext
  have hv : RealTorusSpace.pair A ((1 : ℝ) ⊗ₜ[ℤ] α) (valuation hA a).toAdd =
      (rationalNormLogarithm A.toGrp a).toAdd
        ((rationalCharacters.equivCharacterLattice A).symm α) := by
    rw [← RealTorusSpace.eval_eq_pair]
    have h := BruhatTits.Cartan.centralizerValuation_spec (𝟙 A.toGrp)
      (BruhatTits.Cartan.restrictionEvaluation_id_bijective hA) a
      ((rationalCharacters.equivCharacterLattice A).symm α)
    simpa [BruhatTits.Cartan.characterRestriction, characterRestrict,
      rationalNormLogarithm_eq_intValuation] using h
  have hp :
      (positiveCharacter hA ((1 : ℝ) ⊗ₜ[ℤ] α) a : ℂ) =
        (‖(positiveCharacter hA ((1 : ℝ) ⊗ₜ[ℤ] α) a : ℂ)‖ : ℂ) := by
    rw [positiveCharacter_val, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  rw [hp, positiveCharacter_norm, hv, normalizedAbsoluteValueCharacter_val]
  exact congrArg (fun r : ℝ => (r : ℂ))
    (rationalNormLogarithm_spec A.toGrp a
      ((rationalCharacters.equivCharacterLattice A).symm α)).symm

@[simp] theorem normalizedRealPart_normalizedAbsoluteValueCharacter
    (hA : IsSplitTorus A.toGrp) (α : characterLattice A) :
    normalizedRealPart hA (normalizedAbsoluteValueCharacter α) =
      (1 : ℝ) ⊗ₜ[ℤ] α := by
  rw [normalizedAbsoluteValueCharacter_eq_positiveCharacter hA,
    normalizedRealPart_positiveCharacter]

theorem rawLogRealPart_normalizedAbsoluteValueCharacter
    (hA : IsSplitTorus A.toGrp) (α : characterLattice A) :
    rawLogRealPart hA (normalizedAbsoluteValueCharacter α) =
      (-Real.log (LocalField.residueCardinality F : ℝ)) •
        ((1 : ℝ) ⊗ₜ[ℤ] α) := by
  rw [rawLogRealPart, normalizedRealPart_normalizedAbsoluteValueCharacter]

section RankOne

variable (F)

local notation "𝕋₁" => splitTorus.commGroupScheme (Spec (CommRingCat.of F)) PUnit

/-- The actual algebraic coordinate character of the one-coordinate split torus. -/
def rankOneCoordinateCharacter : characterLattice 𝕋₁ :=
  (splitTorus.characterLatticeEquiv F PUnit).symm (fun _ => 1)

/-- The normalized absolute-value character on the actual one-coordinate split torus. -/
def rankOneAbsoluteValueCharacter : rationalPoints (𝕋₁).toGrp →* ℂˣ :=
  normalizedAbsoluteValueCharacter (rankOneCoordinateCharacter F)

/-- The positive-order uniformizer has normalized real parameter exactly one. -/
theorem rankOne_normalizedRealPart_uniformizer :
    RealTorusSpace.pair 𝕋₁
      (normalizedRealPart (isSplitTorus_splitTorus PUnit)
        (rankOneAbsoluteValueCharacter F))
      (valuation (isSplitTorus_splitTorus PUnit)
        (SplitTorusValuation.uniformizerPoint F)).toAdd = 1 := by
  rw [rankOneAbsoluteValueCharacter, normalizedRealPart_normalizedAbsoluteValueCharacter,
    valuation, BruhatTits.Cartan.centralizerValuation_id_eq_split,
    RealTorusSpace.pair_eq_sum, RealTorusSpace.splitCharacterCoordinates_tmul,
    SplitTorusValuation.splitCocharacterCoordinates_realValuation_uniformizerPoint]
  simp [rankOneCoordinateCharacter]

/-- The same parameter in the raw natural-logarithm convention is `-log q`. -/
theorem rankOne_rawLogRealPart_uniformizer :
    RealTorusSpace.pair 𝕋₁
      (rawLogRealPart (isSplitTorus_splitTorus PUnit)
        (rankOneAbsoluteValueCharacter F))
      (valuation (isSplitTorus_splitTorus PUnit)
        (SplitTorusValuation.uniformizerPoint F)).toAdd =
      -Real.log (LocalField.residueCardinality F : ℝ) := by
  rw [rawLogRealPart, map_smul, LinearMap.smul_apply,
    rankOne_normalizedRealPart_uniformizer, smul_eq_mul, mul_one]

/-- The raw value is the literal natural logarithm of the normalized absolute value. -/
theorem rankOne_log_norm_uniformizer :
    Real.log ‖(rankOneAbsoluteValueCharacter F
      (SplitTorusValuation.uniformizerPoint F) : ℂ)‖ =
      -Real.log (LocalField.residueCardinality F : ℝ) := by
  rw [rankOneAbsoluteValueCharacter,
    normalizedAbsoluteValueCharacter_eq_positiveCharacter
      (isSplitTorus_splitTorus PUnit),
    positiveCharacter_val, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Real.log_exp]
  have h := rankOne_normalizedRealPart_uniformizer F
  rw [rankOneAbsoluteValueCharacter,
    normalizedRealPart_normalizedAbsoluteValueCharacter] at h
  rw [h, neg_mul, one_mul]

end RankOne

end Langlands.Plancherel.SplitTorus
