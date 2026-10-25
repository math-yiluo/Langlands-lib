import Langlands.Representation.Shahidi.LocalCoefficientGeneral
import Langlands.Representation.Shahidi.LocalCoefficientGammaStatement
import Langlands.Representation.Shahidi.GeneralJacquetStatements
import Langlands.Representation.RankinSelberg.GeneralPairGamma

/-!
# Shahidi's Theorem 5.1 over general nonarchimedean local fields

The published actual coefficient and JPSS gamma relations, with the second
representation dualized and with the central-character sign. The analytic
targets normalize the field parameters, require a self-dual Fourier measure,
and state existence of coupled measures. No analytic theorem is assumed.
-/

noncomputable section

namespace Langlands.Shahidi

open MeasureTheory HarmonicAnalysis Whittaker RankinSelberg GeneralLinear GeneralLinear.Iwasawa

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The actual general-field local coefficient equals the JPSS gamma factor
for `(π₁, π̃₂)`, multiplied by `ω(-1)^(m+1)`, with all measures explicit.
Field normalizations and Fourier self-duality are imposed by the statements. -/
def IsGeneralLocalCoefficientGammaComparison
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (hopen : IsOpenNormOne abv)
    (ν : letI := borel F; AdditiveHaarMeasure F)
    {m n : ℕ} {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (m + 1) F) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V₂)
    (ω : Fˣ →* ℂˣ)
    (μ μJ : letI := borel F; Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F))
    (μJ' : letI := borel F; Measure (Matrix (Fin (m + 1)) (Fin (n + 1)) F)) : Prop :=
  ∃ C G : RatFunc ℂ,
    IsGeneralLocalCoefficient q abv hopen π₁ π₂ ψ μ μJ μJ' C ∧
    IsGeneralSymmetricGammaFactor q ψ abv ν π₁ (smoothContragredient π₂) G ∧
    C = ((ω (-1) : ℂˣ) : ℂ) ^ (m + 1) • G

variable (F)

/-- The all-positive-rank part of Shahidi's Theorem 5.1 over any nonarchimedean
local field, with one scalar Haar measure shared by the two Jacquet functionals.
The measures may depend on the factor representations. -/
def GeneralLocalCoefficientGammaAllRanksStatement : Prop :=
  letI := IsTopologicalAddGroup.rightUniformSpace F
  letI := isUniformAddGroup_of_addCommGroup (G := F)
  letI : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  letI := borel F
  letI : BorelSpace F := ⟨rfl⟩
  ∀ (q : ℕ), q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer) →
  ∀ (abv : AbsoluteValue F ℝ) (ϖ : Fˣ), IsUniformizingElement (ValuativeRel.valuation F) ϖ →
    abv (ϖ : F) = (q : ℝ)⁻¹ →
  ∀ (hunit : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1),
  let hopen := isOpenNormOne_of_valuation hunit
  ∀ (ψ : UnitaryAdditiveCharacter F), Conductor.HasIntegerConductor ψ →
  ∀ (ν : AdditiveHaarMeasure F), IsSelfDual ψ ν →
  ∀ (m n : ℕ)
    {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (m + 1) F) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V₂),
    IsGeneric ψ m π₁ → IsGeneric ψ n π₂ →
    ∀ ω : Fˣ →* ℂˣ, Classification.HasGLCentralCharacter F (n + 1) π₂ ω →
    ∃ νI νJ : AdditiveHaarMeasure F,
      IsGeneralLocalCoefficientGammaComparison q ψ abv hopen ν π₁ π₂ ω
        (rectangularMeasure νI (n + 1) (m + 1)) (rectangularMeasure νJ (n + 1) (m + 1))
        (rectangularMeasure νJ (m + 1) (n + 1))

/-- The equal-rank refinement, with the geometric coupling of Shahidi's
pages 75–77 on the actual measures. The recipe is asserted only for ranks
`n+1 ≥ 2`; rank one is covered by the all-rank statement. -/
def GeneralLocalCoefficientGammaEqualRankStatement : Prop :=
  letI := IsTopologicalAddGroup.rightUniformSpace F
  letI := isUniformAddGroup_of_addCommGroup (G := F)
  letI : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  letI := borel F
  letI : BorelSpace F := ⟨rfl⟩
  ∀ (q : ℕ), q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer) →
  ∀ (abv : AbsoluteValue F ℝ) (ϖ : Fˣ), IsUniformizingElement (ValuativeRel.valuation F) ϖ →
    abv (ϖ : F) = (q : ℝ)⁻¹ →
  ∀ (hunit : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1),
  let hopen := isOpenNormOne_of_valuation hunit
  ∀ (ψ : UnitaryAdditiveCharacter F), Conductor.HasIntegerConductor ψ →
  ∀ (ν : AdditiveHaarMeasure F), IsSelfDual ψ ν →
  ∀ (n : ℕ), 0 < n →
  ∀ {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V₂),
    IsGeneric ψ n π₁ → IsGeneric ψ n π₂ →
    ∀ ω : Fˣ →* ℂˣ, Classification.HasGLCentralCharacter F (n + 1) π₂ ω →
    letI := borel Fˣ
    letI := borel (Langlands.GeneralLinear n F)
    haveI : BorelSpace (Langlands.GeneralLinear n F) := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F)
    letI := borel (upperUnipotent n F)
    haveI : BorelSpace (upperUnipotent n F) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F)
    letI := borel (KirillovQuotient n F)
    haveI : BorelSpace (KirillovQuotient n F) := ⟨rfl⟩
    letI := borel (GeneralLinearGroup.integralSubgroup (Fin (n + 1))
      (ValuativeRel.valuation F).integer)
    letI := borel (Langlands.GeneralLinear ((n + 1) + (n + 1)) F)
    ∃ d : EqualRankMeasureData (ValuativeRel.valuation F).integer n,
      IsEqualRankGeometricNormalized ψ abv d ∧
      IsGeneralLocalCoefficientGammaComparison q ψ abv hopen ν π₁ π₂ ω
        d.intertwining d.jacquet d.swappedJacquet

/-- Shahidi's Theorem 5.1, with all positive ranks and the equal-rank
geometric normalization for ranks at least two. Neither component is assumed. -/
def GeneralLocalCoefficientGammaStatement : Prop :=
  GeneralLocalCoefficientGammaAllRanksStatement.{uF, uV} F ∧
  GeneralLocalCoefficientGammaEqualRankStatement.{uF, uV} F

end Langlands.Shahidi
