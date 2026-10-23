import Langlands.Representation.Shahidi.GeneralIntertwiningFamilies
import Langlands.Representation.RankinSelberg.RationalContinuation
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.Whittaker.Iwasawa

/-!
# Convergence and rational continuation over general local fields

These proposition definitions express the analytic assertions following
Shahidi (1984), equation (0.1), using the actual general-field induced spaces.
No convergence or continuation theorem is assumed or proved here.
-/

noncomputable section

namespace Langlands.Shahidi

open GeneralLinear MeasureTheory HarmonicAnalysis SmoothWeakIntegral
  RankinSelberg GeneralLinear.Iwasawa

universe uF uV

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)

/-- The integral (0.1) converges on every section of the actual source induction
on a right half-plane, for irreducible admissible factors and normalized
absolute value over any nonarchimedean local field. -/
def GeneralIntertwiningConvergenceStatement : Prop :=
  letI := borel F
  ∀ (q : ℕ), q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer) →
  ∀ (abv : AbsoluteValue F ℝ) (ϖ : Fˣ), IsUniformizingElement (ValuativeRel.valuation F) ϖ →
    abv (ϖ : F) = (q : ℝ)⁻¹ →
  ∀ (hunit : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1),
  let hopen := isOpenNormOne_of_valuation hunit
  ∀ ν : AdditiveHaarMeasure F,
  ∀ (V₁ V₂ : Type uV) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (GeneralLinear m F) V₁)
    (π₂ : Representation ℂ (GeneralLinear n F) V₂),
    IsAdmissible π₁ → IsSimpleModule (MonoidAlgebra ℂ (GeneralLinear m F)) π₁.asModule →
    IsAdmissible π₂ → IsSimpleModule (MonoidAlgebra ℂ (GeneralLinear n F)) π₂.asModule →
    ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      sourceDomain abv hopen hm hn s π₁ π₂ (rectangularMeasure ν n m) = ⊤

/-- For a flat family, each scalar intertwining coefficient at an integral
matrix agrees on a right half-plane with a rational function of `q^(-s)`.
Convergence on a right half-plane is part of the conclusion. -/
def GeneralIntertwiningRationalityStatement : Prop :=
  letI := borel F
  ∀ (q : ℕ), q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer) →
  ∀ (abv : AbsoluteValue F ℝ) (ϖ : Fˣ), IsUniformizingElement (ValuativeRel.valuation F) ϖ →
    abv (ϖ : F) = (q : ℝ)⁻¹ →
  ∀ (hunit : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1),
  let hopen := isOpenNormOne_of_valuation hunit
  ∀ ν : AdditiveHaarMeasure F,
  ∀ (V₁ V₂ : Type uV) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (GeneralLinear m F) V₁)
    (π₂ : Representation ℂ (GeneralLinear n F) V₂),
    IsAdmissible π₁ → IsSimpleModule (MonoidAlgebra ℂ (GeneralLinear m F)) π₁.asModule →
    IsAdmissible π₂ → IsSimpleModule (MonoidAlgebra ℂ (GeneralLinear n F)) π₂.asModule →
    ∀ f : (∀ s : ℂ, SourceSpace abv hopen hm hn s π₁ π₂),
      IsGeneralFlatFamily abv hopen hm hn π₁ π₂ f →
      (∃ a : ℝ, ∀ s : ℂ, a < s.re →
        f s ∈ sourceDomain abv hopen hm hn s π₁ π₂ (rectangularMeasure ν n m)) ∧
      ∀ k ∈ generalMaximalCompact F (m + n), ∀ ℓ : SmoothDual (pairRepresentation hm hn π₁ π₂),
        ∃ R : RatFunc ℂ, HasRationalContinuation q
          (generalIntertwiningCoefficient abv hopen hm hn π₁ π₂
            (rectangularMeasure ν n m) f k ℓ) R

/-- Both analytic obligations for the same field and positive ranks. -/
def GeneralIntertwiningAnalyticStatement : Prop :=
  GeneralIntertwiningConvergenceStatement.{uF, uV} F hm hn ∧
  GeneralIntertwiningRationalityStatement.{uF, uV} F hm hn

end Langlands.Shahidi
