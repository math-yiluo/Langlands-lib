import Langlands.GroupScheme.MatrixRepresentationPolynomialGrowth
import Langlands.Representation.Plancherel.RationalCharacterValuation
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Polynomial and logarithmic bounds for actual rational characters -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj NNReal

universe u

namespace Langlands.GroupScheme

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}

/-- The global regular function underlying the universal value of an actual
rational character. -/
def rationalCharacterSection (χ : rationalCharacters G) : AffineCoordinateRing F G.X :=
  (characterEval χ G.X (𝟙 G.X)).val

/-- Evaluating the universal character section gives the actual character
value on the same rational point. -/
theorem rationalPointAlgebraHom_rationalCharacterSection [IsAffine G.X.left]
    (χ : rationalCharacters G) (g : rationalPoints G) :
    rationalPointAlgebraHom F G.X g (rationalCharacterSection χ) =
      (rationalCharacterEval χ g : F) := by
  rw [rationalPointAlgebraHom_apply_appTop, rationalCharacterEval_val]
  have h := characterEval_naturality χ g (𝟙 G.X)
  rw [Category.comp_id] at h
  change (Scheme.ΓSpecIso (CommRingCat.of F)).hom
      (g.left.appTop (characterEval χ G.X (𝟙 G.X)).val) = _
  rw [h]
  rfl

namespace MatrixRepresentation

variable (F) [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [IsAffine G.X.left]
  {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Every rational algebraic character has a uniform polynomial bound in any
supplied closed matrix embedding. -/
theorem rationalCharacter_rationalMatrixNorm_powerBound
    (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    (χ : rationalCharacters G) :
    ∃ (d : ℕ) (c : ℝ), 0 < c ∧ ∀ g : rationalPoints G,
      LocalField.residueNormalizedAbsoluteValue F (rationalCharacterEval χ g : F) ≤
        c * rationalMatrixNorm F ρ g ^ d := by
  obtain ⟨d, c, hc, hb⟩ :=
    regularFunction_rationalMatrixNorm_powerBound F ρ hρ (rationalCharacterSection χ)
  exact ⟨d, c, hc, fun g => by
    simpa only [rationalPointAlgebraHom_rationalCharacterSection] using hb g⟩

/-- The logarithm of an actual rational character is bounded in absolute value
by a constant times one plus the logarithm of the actual matrix norm. -/
theorem rationalCharacter_abs_log_rationalMatrixNorm_bound
    (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    (χ : rationalCharacters G) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : rationalPoints G,
      |Real.log (LocalField.residueNormalizedAbsoluteValue F
        (rationalCharacterEval χ g : F))| ≤
          C * (1 + Real.log (rationalMatrixNorm F ρ g)) := by
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  obtain ⟨d, c, hc, hb⟩ := rationalCharacter_rationalMatrixNorm_powerBound F ρ hρ χ
  have hH (g : rationalPoints G) : 0 < rationalMatrixNorm F ρ g :=
    zero_lt_one.trans_le (one_le_rationalMatrixNorm F ρ g)
  have hχ (g : rationalPoints G) :
      0 < LocalField.residueNormalizedAbsoluteValue F (rationalCharacterEval χ g : F) := by
    change 0 < ‖(rationalCharacterEval χ g : F)‖
    exact norm_pos_iff.mpr (Units.ne_zero _)
  have hu (g : rationalPoints G) :
      Real.log (LocalField.residueNormalizedAbsoluteValue F
        (rationalCharacterEval χ g : F)) ≤
          Real.log c + (d : ℝ) * Real.log (rationalMatrixNorm F ρ g) := by
    calc
      _ ≤ Real.log (c * rationalMatrixNorm F ρ g ^ d) :=
        Real.log_le_log (hχ g) (hb g)
      _ = _ := by rw [Real.log_mul hc.ne' (pow_ne_zero _ (hH g).ne'), Real.log_pow]
  let C : ℝ := |Real.log c| + (d : ℝ) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hlogC : Real.log c ≤ C := by
    dsimp [C]
    linarith [le_abs_self (Real.log c), Nat.cast_nonneg (α := ℝ) d]
  have hdC : (d : ℝ) ≤ C := by
    dsimp [C]
    linarith [abs_nonneg (Real.log c)]
  have hupper (g : rationalPoints G) :
      Real.log (LocalField.residueNormalizedAbsoluteValue F
        (rationalCharacterEval χ g : F)) ≤
          C * (1 + Real.log (rationalMatrixNorm F ρ g)) := by
    calc
      _ ≤ Real.log c + (d : ℝ) * Real.log (rationalMatrixNorm F ρ g) := hu g
      _ ≤ C + C * Real.log (rationalMatrixNorm F ρ g) :=
        add_le_add hlogC
          (mul_le_mul_of_nonneg_right hdC
            (Real.log_nonneg (one_le_rationalMatrixNorm F ρ g)))
      _ = _ := by ring
  refine ⟨C, hC, fun g => abs_le.mpr ⟨?_, hupper g⟩⟩
  have hi := hupper g⁻¹
  simp only [map_inv, Units.val_inv_eq_inv_val, map_inv₀, Real.log_inv,
    rationalMatrixNorm_inv] at hi
  linarith

/-- The same bound for the published family of positive normalized rational
characters, as used by the modulus-height estimates. -/
theorem rationalNormCharacters_abs_log_rationalMatrixNorm_bound
    (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    (χ : rationalCharacters G) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : rationalPoints G,
      |Real.log (((Langlands.Plancherel.rationalNormCharacters G χ).toMul g :
        ℝ≥0) : ℝ)| ≤ C * (1 + Real.log (rationalMatrixNorm F ρ g)) := by
  simpa only [Langlands.Plancherel.rationalNormCharacters_val] using
    rationalCharacter_abs_log_rationalMatrixNorm_bound F ρ hρ χ

end MatrixRepresentation

end Langlands.GroupScheme
