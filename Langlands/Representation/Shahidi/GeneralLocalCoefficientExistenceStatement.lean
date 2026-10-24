import Langlands.Representation.Shahidi.LocalCoefficientGeneral
import Langlands.Representation.Shahidi.GeneralJacquetStatements

/-!
# Rational local-coefficient existence over general nonarchimedean local fields

These proposition definitions state the analytic existence obligation for the
published actual general-field local-coefficient relation. The residue cardinality,
absolute value and character are normalized, and the three Haar choices are fixed
independently. No analytic assertion is assumed or proved here.
-/

noncomputable section

namespace Langlands.Shahidi

open MeasureTheory HarmonicAnalysis Whittaker RankinSelberg GeneralLinear.Iwasawa

universe uF uV

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (m n : ℕ)

/-- The rational existence assertion behind Shahidi (1984), (0.3), for the actual
general-field induction. All three Haar measures are arbitrary fixed choices;
this is not the measure-normalized gamma comparison. -/
def GeneralLocalCoefficientExistenceStatement : Prop :=
  letI := borel F
  ∀ (q : ℕ), q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer) →
  ∀ (abv : AbsoluteValue F ℝ) (ϖ : Fˣ), IsUniformizingElement (ValuativeRel.valuation F) ϖ →
    abv (ϖ : F) = (q : ℝ)⁻¹ →
  ∀ (hunit : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1),
  let hopen := isOpenNormOne_of_valuation hunit
  ∀ (ψ : UnitaryAdditiveCharacter F), Conductor.HasIntegerConductor ψ →
  ∀ (ν νJ νJ' : AdditiveHaarMeasure F),
  ∀ (V₁ V₂ : Type uV) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (GeneralLinear (m + 1) F) V₁)
    (π₂ : Representation ℂ (GeneralLinear (n + 1) F) V₂),
    IsGeneric ψ m π₁ → IsGeneric ψ n π₂ →
    ∃ C : RatFunc ℂ, IsGeneralLocalCoefficient q abv hopen π₁ π₂ ψ
      (rectangularMeasure ν (n + 1) (m + 1))
      (rectangularMeasure νJ (n + 1) (m + 1))
      (rectangularMeasure νJ' (m + 1) (n + 1)) C

/-- Stabilization, induced Whittaker multiplicity one, and rational coefficient
existence over a general nonarchimedean local field. None is a premise. -/
def GeneralJacquetAndCoefficientStatement : Prop :=
  GeneralJacquetStatement.{uF, uV} F m n ∧
  GeneralLocalCoefficientExistenceStatement.{uF, uV} F m n

end Langlands.Shahidi
