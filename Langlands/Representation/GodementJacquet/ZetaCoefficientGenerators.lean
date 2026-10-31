import Langlands.Representation.GodementJacquet.ZetaLinear
import Langlands.Representation.GodementJacquet.ProductGenerators

/-! # Smooth coefficient generators for the actual matrix value module -/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory RankinSelberg

universe uF uV uW

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  [MeasurableSpace (GeneralLinear (n + 1) F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Actual shifted rational values obtained from a single smooth functional
and a single smooth vector, before taking a Laurent span. -/
def matrixGeneratorRationalValues (q : ℕ) (abv : AbsoluteValue F ℝ)
    (μ : Measure (GeneralLinear (n + 1) F))
    (σ : Representation ℂ (GeneralLinear (n + 1) F) V) :
    Set RationalFunctions :=
  {R | ∃ (Φ : MatrixTestFunction n F) (ℓ : SmoothDual σ) (v : smoothVectors σ),
    HasShiftedRationalValue q abv μ Φ (biSmoothCoefficient σ ℓ v) R}

variable {q : ℕ} {abv : AbsoluteValue F ℝ}
  {μ : Measure (GeneralLinear (n + 1) F)}
  {σ : Representation ℂ (GeneralLinear (n + 1) F) V}

/-- Every individual smooth coefficient belongs to the actual published
coefficient span. -/
theorem matrixGeneratorRationalValues_subset :
    matrixGeneratorRationalValues q abv μ σ ⊆ matrixRationalValues q abv μ σ := by
  rintro R ⟨Φ, ℓ, v, hR⟩
  exact ⟨Φ, ⟨biSmoothCoefficient σ ℓ v, Submodule.subset_span ⟨ℓ, v, rfl⟩⟩, hR⟩

/-- If every individual smooth coefficient has an actual rational value,
then their values generate the entire published matrix value module.
Continuation uniqueness identifies all values, with their denominator guards. -/
theorem zetaSpan_matrixRationalValues_eq_generatorSpan
    (hq : 1 < q)
    (h : ∀ (Φ : MatrixTestFunction n F) (ℓ : SmoothDual σ) (v : smoothVectors σ),
      ∃ R, HasShiftedRationalValue q abv μ Φ (biSmoothCoefficient σ ℓ v) R) :
    zetaSpan (matrixRationalValues q abv μ σ) =
      zetaSpan (matrixGeneratorRationalValues q abv μ σ) := by
  refine le_antisymm (zetaSpan_matrixRationalValues_le_of_generators hq ?_)
    (zetaSpan_mono matrixGeneratorRationalValues_subset)
  intro Φ ℓ v
  obtain ⟨R, hR⟩ := h Φ ℓ v
  exact ⟨R, hR, mem_zetaSpan ⟨Φ, ℓ, v, hR⟩⟩

/-- The full analytic predicate supplies the rationality premise of the
generator-span equality without any extra admissibility hypothesis. -/
theorem MatrixAnalyticAssertions.zetaSpan_eq_generatorSpan
    {P : Polynomial ℂ} (h : MatrixAnalyticAssertions q abv μ σ P) (hq : 1 < q) :
    zetaSpan (matrixRationalValues q abv μ σ) =
      zetaSpan (matrixGeneratorRationalValues q abv μ σ) := by
  apply zetaSpan_matrixRationalValues_eq_generatorSpan hq
  intro Φ ℓ v
  exact h.2.1 Φ
    ⟨biSmoothCoefficient σ ℓ v, Submodule.subset_span ⟨ℓ, v, rfl⟩⟩

section Products

variable {n₀ n₁ : ℕ}
  [MeasurableSpace (GeneralLinear (n₀ + 1) F)]
  [MeasurableSpace (GeneralLinear (n₁ + 1) F)]
  {V₀ : Type uV} [AddCommGroup V₀] [Module ℂ V₀]
  {V₁ : Type uW} [AddCommGroup V₁] [Module ℂ V₁]
  {μ₀ : Measure (GeneralLinear (n₀ + 1) F)}
  {μ₁ : Measure (GeneralLinear (n₁ + 1) F)}
  {σ₀ : Representation ℂ (GeneralLinear (n₀ + 1) F) V₀}
  {σ₁ : Representation ℂ (GeneralLinear (n₁ + 1) F) V₁}

/-- To contain the product of the full block value modules, it suffices to
contain products from individual smooth block coefficients. This retains
arbitrary tests, their actual rational values and both denominator guards. -/
theorem zetaSpan_matrixRationalValues_mul_le_of_generator_products
    (hq : 1 < q)
    (h₀ : ∀ (Φ : MatrixTestFunction n₀ F) (ℓ : SmoothDual σ₀) (v : smoothVectors σ₀),
      ∃ R, HasShiftedRationalValue q abv μ₀ Φ (biSmoothCoefficient σ₀ ℓ v) R)
    (h₁ : ∀ (Φ : MatrixTestFunction n₁ F) (ℓ : SmoothDual σ₁) (v : smoothVectors σ₁),
      ∃ R, HasShiftedRationalValue q abv μ₁ Φ (biSmoothCoefficient σ₁ ℓ v) R)
    {W : Submodule LaurentCoefficients RationalFunctions}
    (hprod : ∀ (Φ₀ : MatrixTestFunction n₀ F) (ℓ₀ : SmoothDual σ₀)
      (v₀ : smoothVectors σ₀) (Φ₁ : MatrixTestFunction n₁ F) (ℓ₁ : SmoothDual σ₁)
      (v₁ : smoothVectors σ₁) (R S : RationalFunctions),
      HasShiftedRationalValue q abv μ₀ Φ₀ (biSmoothCoefficient σ₀ ℓ₀ v₀) R →
      HasShiftedRationalValue q abv μ₁ Φ₁ (biSmoothCoefficient σ₁ ℓ₁ v₁) S →
      R * S ∈ W) :
    zetaSpan (matrixRationalValues q abv μ₀ σ₀) *
      zetaSpan (matrixRationalValues q abv μ₁ σ₁) ≤ W := by
  rw [zetaSpan_matrixRationalValues_eq_generatorSpan hq h₀,
    zetaSpan_matrixRationalValues_eq_generatorSpan hq h₁,
    ← zetaSpan_productRationalValues]
  apply Submodule.span_le.mpr
  rintro _ ⟨R, ⟨Φ₀, ℓ₀, v₀, hR⟩, S, ⟨Φ₁, ℓ₁, v₁, hS⟩, rfl⟩
  exact hprod Φ₀ ℓ₀ v₀ Φ₁ ℓ₁ v₁ R S hR hS

end Products

end Langlands.GodementJacquet
