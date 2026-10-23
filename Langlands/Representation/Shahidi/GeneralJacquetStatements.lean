import Langlands.Representation.Shahidi.JacquetInduced
import Langlands.Representation.Conductor.Essential

/-!
# Jacquet stabilization over general nonarchimedean local fields

These are analytic proposition definitions over the actual general-field source
and target inductions, including positive characteristic. No analytic proof is
assumed by the definitions.
-/

noncomputable section

namespace Langlands.Shahidi

open MeasureTheory HarmonicAnalysis Whittaker RankinSelberg GeneralLinear.Iwasawa

universe uF uV

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (m n : ℕ)

/-- Shahidi (1984), (0.2) and the paragraph after (1.1): both induced Jacquet
integrals stabilize, and define nonzero standard Whittaker functionals at every
complex parameter. The two Haar measures are kept explicit and independent. -/
def GeneralJacquetStabilizationStatement : Prop :=
  letI := borel F
  ∀ (q : ℕ), q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer) →
  ∀ (abv : AbsoluteValue F ℝ) (ϖ : Fˣ), IsUniformizingElement (ValuativeRel.valuation F) ϖ →
    abv (ϖ : F) = (q : ℝ)⁻¹ →
  ∀ (hunit : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1),
  let hopen := isOpenNormOne_of_valuation hunit
  ∀ (ψ : UnitaryAdditiveCharacter F), Conductor.HasIntegerConductor ψ →
  ∀ (νJ νJ' : AdditiveHaarMeasure F),
  ∀ (V₁ V₂ : Type uV) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (GeneralLinear (m + 1) F) V₁)
    (π₂ : Representation ℂ (GeneralLinear (n + 1) F) V₂),
    IsGeneric ψ m π₁ → IsGeneric ψ n π₂ →
    ∀ ℓ₁ ∈ glFunctionals ψ m π₁, ∀ ℓ₂ ∈ glFunctionals ψ n π₂,
      ℓ₁ ≠ 0 → ℓ₂ ≠ 0 → ∀ s : ℂ,
      (∃ Λ : SourceSpace abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ →ₗ[ℂ] ℂ,
        IsSourceJacquetFunctional abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂
          (rectangularMeasure νJ (n + 1) (m + 1)) Λ ∧
        Λ ∈ glFunctionals ψ (m + 1 + n)
          (source abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂) ∧ Λ ≠ 0) ∧
      (∃ Λ' : TargetSpace abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ →ₗ[ℂ] ℂ,
        IsTargetJacquetFunctional abv hopen s π₁ π₂ ψ ℓ₁ ℓ₂
          (rectangularMeasure νJ' (m + 1) (n + 1)) Λ' ∧
        Λ' ∈ glFunctionals ψ (m + 1 + n)
          (target abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂) ∧ Λ' ≠ 0)

/-- The induced multiplicity-one input behind (0.3): any nonzero standard
Whittaker functional spans the entire Whittaker space, for either induced
representation and every complex parameter. This is an analytic theorem target,
not an irreducibility assumption on the possibly reducible induced spaces. -/
def GeneralInducedWhittakerMultiplicityOneStatement : Prop :=
  ∀ (q : ℕ), q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer) →
  ∀ (abv : AbsoluteValue F ℝ) (ϖ : Fˣ), IsUniformizingElement (ValuativeRel.valuation F) ϖ →
    abv (ϖ : F) = (q : ℝ)⁻¹ →
  ∀ (hunit : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1),
  let hopen := isOpenNormOne_of_valuation hunit
  ∀ (ψ : UnitaryAdditiveCharacter F), Conductor.HasIntegerConductor ψ →
  ∀ (V₁ V₂ : Type uV) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (GeneralLinear (m + 1) F) V₁)
    (π₂ : Representation ℂ (GeneralLinear (n + 1) F) V₂),
    IsGeneric ψ m π₁ → IsGeneric ψ n π₂ → ∀ s : ℂ,
      (∀ Λ ∈ glFunctionals ψ (m + 1 + n)
          (source abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂), Λ ≠ 0 →
        ∀ L ∈ glFunctionals ψ (m + 1 + n)
          (source abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂),
          ∃ a : ℂ, L = a • Λ) ∧
      (∀ Λ' ∈ glFunctionals ψ (m + 1 + n)
          (target abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂), Λ' ≠ 0 →
        ∀ L' ∈ glFunctionals ψ (m + 1 + n)
          (target abv hopen (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂),
          ∃ a : ℂ, L' = a • Λ')

/-- Both analytic obligations, with none assumed as a premise. -/
def GeneralJacquetStatement : Prop :=
  GeneralJacquetStabilizationStatement.{uF, uV} F m n ∧
  GeneralInducedWhittakerMultiplicityOneStatement.{uF, uV} F m n

end Langlands.Shahidi
