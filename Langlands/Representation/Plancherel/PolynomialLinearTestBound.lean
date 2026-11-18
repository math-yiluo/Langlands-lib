import Langlands.Representation.Plancherel.RationalUnramifiedVectorCancellation
import Mathlib.Analysis.Normed.Operator.Basic

/-! # Bounds for algebraic linear tests of polynomial vector numerators -/

noncomputable section

open scoped NNReal

namespace Langlands.Plancherel.UnramifiedOperatorFamily

universe uL uI uW

variable {L : Type uL} [Group L] [TopologicalSpace L]
  {I : Type uI} {ν : I → (L →* ℝ≥0ˣ)}
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {U : Set (unramifiedCharacters ν)}

/-- The intrinsic value span of a vector family, without choosing a particular
polynomial expansion. -/
def polynomialValueSpan (f : U → W) : Submodule ℂ W :=
  Submodule.span ℂ (Set.range f)

theorem mem_polynomialValueSpan (f : U → W) (z : U) :
    f z ∈ polynomialValueSpan f :=
  Submodule.subset_span ⟨z, rfl⟩

/-- A finite polynomial expansion makes the entire value span finite
dimensional, even when the ambient carrier is infinite dimensional. -/
theorem IsPolynomialOn.finiteDimensional_valueSpan
    {f : U → W} (hf : IsPolynomialOn U f) :
    FiniteDimensional ℂ (polynomialValueSpan f) := by
  obtain ⟨n, b, v, hnum⟩ := hf
  let S : Submodule ℂ W := Submodule.span ℂ (Set.range v)
  let := FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  have hle : polynomialValueSpan f ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    rw [hnum z]
    exact S.sum_mem (fun i _ => S.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩))
  exact Submodule.finiteDimensional_of_le hle

section Normed

variable {E : Type uW} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- An arbitrary algebraic linear test becomes a continuous linear map on the
finite-dimensional value span of a polynomial numerator. -/
def linearTestOnPolynomialSpan (f : U → E) (hf : IsPolynomialOn U f)
    (ℓ : E →ₗ[ℂ] ℂ) : polynomialValueSpan f →L[ℂ] ℂ := by
  letI := hf.finiteDimensional_valueSpan
  exact LinearMap.toContinuousLinearMap (ℓ.comp (polynomialValueSpan f).subtype)

@[simp]
theorem linearTestOnPolynomialSpan_apply (f : U → E) (hf : IsPolynomialOn U f)
    (ℓ : E →ₗ[ℂ] ℂ) (v : polynomialValueSpan f) :
    linearTestOnPolynomialSpan f hf ℓ v = ℓ v := rfl

/-- Each algebraic test of a polynomial vector numerator has a uniform norm
bound on all its values. Continuity of that test on the whole carrier is
neither assumed nor needed. -/
theorem IsPolynomialOn.exists_linear_test_norm_bound
    {f : U → E} (hf : IsPolynomialOn U f) (ℓ : E →ₗ[ℂ] ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : U, ‖ℓ (f z)‖ ≤ C * ‖f z‖ := by
  let T := linearTestOnPolynomialSpan f hf ℓ
  refine ⟨‖T‖, norm_nonneg T, ?_⟩
  intro z
  exact T.le_opNorm ⟨f z, mem_polynomialValueSpan f z⟩

/-- A cleared vector numerator bound yields a cleared scalar bound for every
algebraic linear test. The scalar constant may depend on the test, while the
regular denominator is unchanged. -/
theorem IsPolynomialOn.exists_linear_test_denominator_bound
    {f : U → E} (hf : IsPolynomialOn U f) (ℓ : E →ₗ[ℂ] ℂ)
    (b : unramifiedRegularFunctions ν) (D : Set U) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ z ∈ D, ‖f z‖ ≤ A * ‖b.val z.val‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ D, ‖ℓ (f z)‖ ≤ C * ‖b.val z.val‖ := by
  obtain ⟨C, hC, htest⟩ := hf.exists_linear_test_norm_bound ℓ
  refine ⟨C * A, mul_nonneg hC hA, ?_⟩
  intro z hz
  exact (htest z).trans
    ((mul_le_mul_of_nonneg_left (hbound z hz) hC).trans_eq (mul_assoc C A _).symm)

end Normed

end Langlands.Plancherel.UnramifiedOperatorFamily
