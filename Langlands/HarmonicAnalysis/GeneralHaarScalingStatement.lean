import Langlands.Representation.Shahidi.IntertwiningInduced
import Langlands.Representation.Whittaker.Iwasawa
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Residue-normalized additive Haar scaling over general local fields

Internal prerequisite statements for the general-field Shahidi intertwining
operator, over every nonarchimedean local field, including positive
characteristic. The absolute value is normalized by the residue cardinality
of the specified valuation ring. These definitions state the scalar,
rectangular and block-modulus change-of-variables identities; they do not
prove them.
-/

open scoped NNReal
open MeasureTheory

namespace Langlands.HarmonicAnalysis

open GeneralLinear.Iwasawa

universe uF

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Multiplication by a field unit `a` pushes every Borel additive Haar measure
forward to `|a|⁻¹` times itself, for the residue-normalized absolute value. -/
def GeneralScalarHaarScalingStatement : Prop :=
  ∀ (q : ℕ), q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer) →
  ∀ (abv : AbsoluteValue F ℝ) (ϖ : Fˣ), IsUniformizingElement (ValuativeRel.valuation F) ϖ →
    abv (ϖ : F) = (q : ℝ)⁻¹ →
    (∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1) →
  ∀ [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure] (a : Fˣ),
    μ.map (fun x => (a : F) * x) = ((Shahidi.absUnits abv a : ℝ≥0)⁻¹) • μ

/-- For all ranks `r, s`, including zero, `X ↦ A * X * B⁻¹` pushes every Borel
additive Haar measure on `r × s` matrices forward to
`(|det A|^s / |det B|^r)⁻¹` times itself. -/
def GeneralRectangularHaarScalingStatement : Prop :=
  ∀ (q : ℕ), q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer) →
  ∀ (abv : AbsoluteValue F ℝ) (ϖ : Fˣ), IsUniformizingElement (ValuativeRel.valuation F) ϖ →
    abv (ϖ : F) = (q : ℝ)⁻¹ →
    (∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1) →
  ∀ (r s : ℕ) [MeasurableSpace (Matrix (Fin r) (Fin s) F)]
    [BorelSpace (Matrix (Fin r) (Fin s) F)]
    (μ : Measure (Matrix (Fin r) (Fin s) F)) [μ.IsAddHaarMeasure]
    (A : GeneralLinear r F) (B : GeneralLinear s F),
    μ.map (fun X => (A : Matrix (Fin r) (Fin r) F) * X *
      ((B⁻¹ : GeneralLinear s F) : Matrix (Fin s) (Fin s) F)) =
      (((Shahidi.determinantAbs abv r A : ℝ≥0) ^ s /
        (Shahidi.determinantAbs abv s B : ℝ≥0) ^ r)⁻¹) • μ

/-- For positive ranks `m, n`, every additive Haar measure on `n × m` matrices,
for the product of a Borel measurable structure on the field, satisfies the
Jacobian law `IsModulusScaling` of Shahidi's intertwining integral. -/
def GeneralModulusScalingStatement : Prop :=
  ∀ (q : ℕ), q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer) →
  ∀ (abv : AbsoluteValue F ℝ) (ϖ : Fˣ), IsUniformizingElement (ValuativeRel.valuation F) ϖ →
    abv (ϖ : F) = (q : ℝ)⁻¹ →
    (∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1) →
  ∀ (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    [MeasurableSpace F] [BorelSpace F] [MeasurableAdd₂ F]
    (μ : Measure (Matrix (Fin n) (Fin m) F)) [μ.IsAddHaarMeasure],
    Shahidi.IsModulusScaling hm hn abv μ

/-- The scalar, rectangular and block-modulus Haar scaling prerequisites, with
none assumed as a premise. -/
def GeneralAdditiveHaarScalingStatement : Prop :=
  GeneralScalarHaarScalingStatement.{uF} F ∧
  GeneralRectangularHaarScalingStatement.{uF} F ∧
  GeneralModulusScalingStatement.{uF} F

end Langlands.HarmonicAnalysis
