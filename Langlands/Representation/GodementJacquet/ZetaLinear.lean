import Langlands.Representation.GodementJacquet.AnalyticData
import Langlands.Representation.RankinSelberg.RationalContinuationLinearProof

/-! # Linear closure of actual matrix zeta integrals -/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory RankinSelberg
open RankinSelberg.RationalContinuationLinear

universe uF uV

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  {abv : AbsoluteValue F ℝ}
  {Φ : MatrixTestFunction n F} {s : ℂ}
  {f g : GeneralLinear (n + 1) F → ℂ}

@[simp] theorem matrixIntegrand_zero :
    matrixIntegrand abv Φ s 0 = 0 := by
  funext x
  simp [matrixIntegrand]

theorem matrixIntegrand_add :
    matrixIntegrand abv Φ s (f + g) =
      matrixIntegrand abv Φ s f + matrixIntegrand abv Φ s g := by
  funext x
  simp [matrixIntegrand, mul_add, add_mul]

theorem matrixIntegrand_smul (c : ℂ) :
    matrixIntegrand abv Φ s (c • f) = c • matrixIntegrand abv Φ s f := by
  funext x
  simp only [matrixIntegrand, Pi.smul_apply, smul_eq_mul]
  ring

variable [MeasurableSpace (GeneralLinear (n + 1) F)]
  {μ : Measure (GeneralLinear (n + 1) F)}

theorem matrixConverges_zero : MatrixConverges abv μ Φ s 0 := by
  simp [MatrixConverges]

theorem MatrixConverges.add
    (hf : MatrixConverges abv μ Φ s f) (hg : MatrixConverges abv μ Φ s g) :
    MatrixConverges abv μ Φ s (f + g) := by
  rw [MatrixConverges, matrixIntegrand_add]
  exact Integrable.add hf hg

theorem MatrixConverges.smul (hf : MatrixConverges abv μ Φ s f) (c : ℂ) :
    MatrixConverges abv μ Φ s (c • f) := by
  rw [MatrixConverges, matrixIntegrand_smul]
  exact Integrable.smul c hf

theorem matrixIntegral_add
    (hf : MatrixConverges abv μ Φ s f) (hg : MatrixConverges abv μ Φ s g) :
    matrixIntegral abv μ Φ s (f + g) =
      matrixIntegral abv μ Φ s f + matrixIntegral abv μ Φ s g := by
  unfold matrixIntegral
  rw [matrixIntegrand_add]
  exact integral_add hf hg

theorem matrixIntegral_smul (c : ℂ) :
    matrixIntegral abv μ Φ s (c • f) = c * matrixIntegral abv μ Φ s f := by
  unfold matrixIntegral
  rw [matrixIntegrand_smul]
  exact integral_const_mul c _

/-- Functions whose actual matrix integrand is integrable for the fixed test
and parameter form a complex submodule. -/
def matrixConvergenceSubmodule (abv : AbsoluteValue F ℝ)
    (μ : Measure (GeneralLinear (n + 1) F)) (Φ : MatrixTestFunction n F) (s : ℂ) :
    Submodule ℂ (GeneralLinear (n + 1) F → ℂ) where
  carrier := {f | MatrixConverges abv μ Φ s f}
  zero_mem' := matrixConverges_zero
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c _ hf => hf.smul c

/-- Integrability on a set of functions extends to its entire complex span. -/
theorem matrixConverges_of_mem_span
    {A : Set (GeneralLinear (n + 1) F → ℂ)}
    (hA : ∀ f ∈ A, MatrixConverges abv μ Φ s f)
    (hf : f ∈ Submodule.span ℂ A) :
    MatrixConverges abv μ Φ s f :=
  (show Submodule.span ℂ A ≤ matrixConvergenceSubmodule abv μ Φ s from
    Submodule.span_le.mpr hA) hf

theorem hasShiftedRationalValue_zero (q : ℕ) :
    HasShiftedRationalValue q abv μ Φ 0 0 := by
  constructor
  · exact ⟨0, fun _ _ => matrixConverges_zero⟩
  · refine ⟨0, fun s _ => ?_⟩
    simp [matrixIntegral]

/-- Actual shifted rational values add, with convergence and denominator
nonvanishing retained on a common right half-plane. -/
theorem HasShiftedRationalValue.add {q : ℕ} {R S : RationalFunctions}
    (hR : HasShiftedRationalValue q abv μ Φ f R)
    (hS : HasShiftedRationalValue q abv μ Φ g S) :
    HasShiftedRationalValue q abv μ Φ (f + g) (R + S) := by
  obtain ⟨⟨a, ha⟩, hR⟩ := hR
  obtain ⟨⟨b, hb⟩, hS⟩ := hS
  refine ⟨⟨max a b, fun s hs =>
    (ha s ((le_max_left a b).trans_lt hs)).add
      (hb s ((le_max_right a b).trans_lt hs))⟩, ?_⟩
  exact continuation_of_eq_on_right (continuation_add hR hS)
    ⟨max a b, fun s hs =>
      matrixIntegral_add (ha s ((le_max_left a b).trans_lt hs))
        (hb s ((le_max_right a b).trans_lt hs))⟩

/-- Constant multiples preserve actual shifted rational values, including
zero scalars. -/
theorem HasShiftedRationalValue.smul {q : ℕ} {R : RationalFunctions}
    (hR : HasShiftedRationalValue q abv μ Φ f R) (c : ℂ) :
    HasShiftedRationalValue q abv μ Φ (c • f) (RatFunc.C c * R) := by
  obtain ⟨⟨a, ha⟩, hR⟩ := hR
  refine ⟨⟨a, fun s hs => (ha s hs).smul c⟩, ?_⟩
  exact continuation_of_eq_on_right (hasRationalContinuation_const_mul c hR)
    ⟨0, fun _ _ => matrixIntegral_smul c⟩

/-- Coefficients admitting an actual shifted rational value in a prescribed
Laurent submodule form a complex submodule. -/
def matrixRationalCoefficientSubmodule (q : ℕ) (abv : AbsoluteValue F ℝ)
    (μ : Measure (GeneralLinear (n + 1) F)) (Φ : MatrixTestFunction n F)
    (W : Submodule LaurentCoefficients RationalFunctions) :
    Submodule ℂ (GeneralLinear (n + 1) F → ℂ) where
  carrier := {f | ∃ R, HasShiftedRationalValue q abv μ Φ f R ∧ R ∈ W}
  zero_mem' := ⟨0, hasShiftedRationalValue_zero q, W.zero_mem⟩
  add_mem' := by
    rintro f g ⟨R, hR, hRW⟩ ⟨S, hS, hSW⟩
    exact ⟨R + S, hR.add hS, W.add_mem hRW hSW⟩
  smul_mem' := by
    rintro c f ⟨R, hR, hRW⟩
    refine ⟨RatFunc.C c * R, hR.smul c, ?_⟩
    simpa only [Algebra.smul_def, algebraMap_laurent, laurentToRatFunc_C] using
      W.smul_mem (LaurentPolynomial.C c) hRW

/-- Existence of actual rational values in one Laurent submodule extends from
generators to their entire complex span. -/
theorem hasShiftedRationalValue_mem_of_mem_span
    {q : ℕ} {W : Submodule LaurentCoefficients RationalFunctions}
    {A : Set (GeneralLinear (n + 1) F → ℂ)}
    (hA : ∀ f ∈ A, ∃ R, HasShiftedRationalValue q abv μ Φ f R ∧ R ∈ W)
    (hf : f ∈ Submodule.span ℂ A) :
    ∃ R, HasShiftedRationalValue q abv μ Φ f R ∧ R ∈ W :=
  (show Submodule.span ℂ A ≤ matrixRationalCoefficientSubmodule q abv μ Φ W from
    Submodule.span_le.mpr hA) hf

section Representation

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {σ : Representation ℂ (GeneralLinear (n + 1) F) V}

/-- A uniform right half-plane for individual smooth coefficients is exactly
a uniform right half-plane for the full bi-smooth coefficient span. -/
theorem matrixConvergesOnRight_iff_generators :
    MatrixConvergesOnRight abv μ σ ↔
      ∃ a : ℝ, ∀ Φ : MatrixTestFunction n F,
        ∀ (ℓ : SmoothDual σ) (v : smoothVectors σ),
          ∀ s : ℂ, a < s.re →
            MatrixConverges abv μ Φ (s + jpssShift n) (biSmoothCoefficient σ ℓ v) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, fun Φ ℓ v s hs =>
      ha Φ ⟨biSmoothCoefficient σ ℓ v, Submodule.subset_span ⟨ℓ, v, rfl⟩⟩ s hs⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, fun Φ f s hs => matrixConverges_of_mem_span ?_ f.property⟩
    rintro g ⟨ℓ, v, rfl⟩
    exact ha Φ ℓ v s hs

/-- A generator-by-generator rationality and value-module calculation suffices
for all actual bi-smooth coefficients, without admissibility assumptions. -/
theorem exists_hasShiftedRationalValue_mem_of_generators
    {q : ℕ} {W : Submodule LaurentCoefficients RationalFunctions}
    (h : ∀ (ℓ : SmoothDual σ) (v : smoothVectors σ),
      ∃ R, HasShiftedRationalValue q abv μ Φ (biSmoothCoefficient σ ℓ v) R ∧ R ∈ W)
    (f : biSmoothMatrixCoefficients σ) :
    ∃ R, HasShiftedRationalValue q abv μ Φ f.val R ∧ R ∈ W := by
  apply hasShiftedRationalValue_mem_of_mem_span (f := f.val) _ f.property
  rintro g ⟨ℓ, v, rfl⟩
  exact h ℓ v

/-- When `q > 1`, continuation uniqueness upgrades generator value-module
containment to containment of the entire published Laurent span. -/
theorem zetaSpan_matrixRationalValues_le_of_generators
    {q : ℕ} (hq : 1 < q) {W : Submodule LaurentCoefficients RationalFunctions}
    (h : ∀ (Φ : MatrixTestFunction n F) (ℓ : SmoothDual σ) (v : smoothVectors σ),
      ∃ R, HasShiftedRationalValue q abv μ Φ (biSmoothCoefficient σ ℓ v) R ∧ R ∈ W) :
    zetaSpan (matrixRationalValues q abv μ σ) ≤ W := by
  apply Submodule.span_le.mpr
  rintro R ⟨Φ, f, hR⟩
  obtain ⟨S, hS, hSW⟩ := exists_hasShiftedRationalValue_mem_of_generators (h Φ) f
  exact (hR.2.unique hq hS.2) ▸ hSW

end Representation

end Langlands.GodementJacquet
