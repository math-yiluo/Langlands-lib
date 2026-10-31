import Langlands.Representation.GodementJacquet.ZetaCoefficientGenerators

/-!
# Assembly of the full two-block matrix analytic predicate

The analytic hypotheses here concern actual individual smooth coefficients.
The conclusion concerns the whole published coefficient span and both
inclusions in its normalized Laurent generator equality.
-/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory RankinSelberg

universe uF uV uW

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {t : ℕ} [MeasurableSpace (GeneralLinear (t + 1) F)]
  {U : Type uW} [AddCommGroup U] [Module ℂ U]

/-- The three actual generator inputs for two-block analytic assembly:
common shifted convergence, forward product-module rationality and reverse
realization of individual block values. -/
def TwoBlockMatrixGeneratorInputs
    (q : ℕ) (abv : AbsoluteValue F ℝ)
    (μind : Measure (GeneralLinear (t + 1) F))
    (π : Representation ℂ (GeneralLinear (t + 1) F) U)
    (m : Fin 2 → ℕ) [∀ i, MeasurableSpace (GeneralLinear (m i + 1) F)]
    {V : Fin 2 → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (μ : ∀ i, Measure (GeneralLinear (m i + 1) F))
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (V i)) : Prop :=
    (∃ a : ℝ, ∀ (Φ : MatrixTestFunction t F)
      (ℓ : SmoothDual π) (v : smoothVectors π) (s : ℂ),
      a < s.re →
        MatrixConverges abv μind Φ (s + jpssShift t) (biSmoothCoefficient π ℓ v)) ∧
    (∀ (Φ : MatrixTestFunction t F)
      (ℓ : SmoothDual π) (v : smoothVectors π),
      ∃ R, HasShiftedRationalValue q abv μind Φ (biSmoothCoefficient π ℓ v) R ∧
        R ∈ zetaSpan (matrixRationalValues q abv (μ 0) (σ 0)) *
          zetaSpan (matrixRationalValues q abv (μ 1) (σ 1))) ∧
    (∀ (Φ₀ : MatrixTestFunction (m 0) F)
      (ℓ₀ : SmoothDual (σ 0)) (v₀ : smoothVectors (σ 0))
      (Φ₁ : MatrixTestFunction (m 1) F)
      (ℓ₁ : SmoothDual (σ 1)) (v₁ : smoothVectors (σ 1))
      (R S : RationalFunctions),
      HasShiftedRationalValue q abv (μ 0) Φ₀ (biSmoothCoefficient (σ 0) ℓ₀ v₀) R →
      HasShiftedRationalValue q abv (μ 1) Φ₁ (biSmoothCoefficient (σ 1) ℓ₁ v₁) S →
      R * S ∈ zetaSpan (matrixRationalValues q abv μind π))

/-- The actual generator inputs and block analytic predicates imply the
entire analytic predicate, including both normalized-generator inclusions. -/
theorem matrixAnalyticAssertions_twoBlock_of_generators
    (q : ℕ) (hq : 1 < q) (abv : AbsoluteValue F ℝ)
    (μind : Measure (GeneralLinear (t + 1) F))
    (π : Representation ℂ (GeneralLinear (t + 1) F) U)
    (m : Fin 2 → ℕ) [∀ i, MeasurableSpace (GeneralLinear (m i + 1) F)]
    {V : Fin 2 → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (μ : ∀ i, Measure (GeneralLinear (m i + 1) F))
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (V i))
    (P : Fin 2 → Polynomial ℂ)
    (hblock : ∀ i, MatrixAnalyticAssertions q abv (μ i) (σ i) (P i))
    (h : TwoBlockMatrixGeneratorInputs q abv μind π m μ σ) :
    MatrixAnalyticAssertions q abv μind π (∏ i, P i) := by
  obtain ⟨hconv, hforward, hreverse⟩ := h
  have hrat := fun (Φ : MatrixTestFunction t F) (f : biSmoothMatrixCoefficients π) =>
    exists_hasShiftedRationalValue_mem_of_generators (hforward Φ) f
  refine ⟨matrixConvergesOnRight_iff_generators.mpr hconv,
    fun Φ f => (hrat Φ f).imp (fun _ h => h.1), ?_⟩
  apply normalizedGenerator_twoBlock_of_span_eq
    (fun i => matrixRationalValues q abv (μ i) (σ i)) P
    (fun i => (hblock i).2.2)
  apply le_antisymm (zetaSpan_matrixRationalValues_le_of_generators hq hforward)
  apply zetaSpan_matrixRationalValues_mul_le_of_generator_products hq
    (hprod := hreverse)
  · intro Φ ℓ v
    exact (hblock 0).2.1 Φ
      ⟨biSmoothCoefficient (σ 0) ℓ v, Submodule.subset_span ⟨ℓ, v, rfl⟩⟩
  · intro Φ ℓ v
    exact (hblock 1).2.1 Φ
      ⟨biSmoothCoefficient (σ 1) ℓ v, Submodule.subset_span ⟨ℓ, v, rfl⟩⟩

end Langlands.GodementJacquet
