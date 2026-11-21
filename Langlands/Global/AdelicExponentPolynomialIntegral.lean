import Langlands.Representation.Archimedean.RealInductionStagesFamily
import Langlands.Global.AdelicLeadingCuspidalComponents
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Parameterized integrals of exponent polynomials -/

noncomputable section

open scoped BigOperators
open MeasureTheory

set_option autoImplicit false

namespace Langlands.Global

section Polynomial

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Composing an exponent polynomial with a real-linear log map preserves its
degree bound. -/
theorem polynomialFunctions_comp_linear (L : W →ₗ[ℝ] V) {n : ℕ} {p : V → ℂ}
    (hp : p ∈ polynomialFunctions V n) : p ∘ L ∈ polynomialFunctions W n := by
  let pull : (V → ℂ) →ₗ[ℂ] (W → ℂ) := LinearMap.funLeft ℂ ℂ L
  apply (show polynomialFunctions V n ≤ (polynomialFunctions W n).comap pull from ?_) hp
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, hk, forms, rfl⟩
  exact Submodule.subset_span ⟨k, hk, fun i => (forms i).comp L, rfl⟩

/-- Products of at most `n` coordinate functions span the bounded-degree
polynomials on a finite-dimensional real logarithm space. -/
theorem finiteDimensional_polynomialFunctions [FiniteDimensional ℝ V] (n : ℕ) :
    FiniteDimensional ℂ (polynomialFunctions V n) := by
  classical
  let I := Fin (Module.finrank ℝ V)
  let b : Module.Basis I ℝ V := Module.finBasis ℝ V
  let word : (Σ k : Fin (n + 1), Fin k.val → I) → V → ℂ :=
    fun w x => ∏ j : Fin w.1.val, (b.repr x (w.2 j) : ℂ)
  let S := Submodule.span ℂ (Set.range word)
  let : FiniteDimensional ℂ S := Module.Finite.span_of_finite ℂ (Set.finite_range word)
  apply Submodule.finiteDimensional_of_le (S₂ := S)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, hk, forms, rfl⟩
  let degree : Fin (n + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
  have hform (j : Fin k) (x : V) :
      (forms j x : ℂ) = ∑ i : I, (forms j (b i) : ℂ) * (b.repr x i : ℂ) := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hprod : (fun x : V => ∏ j : Fin k, (forms j x : ℂ)) =
      ∑ idx : Fin k → I, (∏ j, (forms j (b (idx j)) : ℂ)) • word ⟨degree, idx⟩ := by
    funext x
    have h := Finset.prod_congr (s₂ := Finset.univ) rfl (fun j _ => hform j x)
    rw [h, Fintype.prod_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun idx _ => Finset.prod_mul_distrib
  rw [hprod]
  exact S.sum_mem fun idx _ => S.smul_mem _ (Submodule.subset_span ⟨⟨degree, idx⟩, rfl⟩)

end Polynomial

section Integration

variable {X Ω : Type*} [MeasurableSpace Ω]

/-- A pointwise integrable family of degree-bounded exponent polynomials has
an integral with the same degree bound. -/
def ExponentPolynomialIntegralStatement : Prop :=
  ∀ {V Ω : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace Ω] (n : ℕ) (f : Ω → V → ℂ) (μ : Measure Ω),
    (∀ t, f t ∈ polynomialFunctions V n) → (∀ x, Integrable (fun t => f t x) μ) →
    (fun x => ∫ t, f t x ∂μ) ∈ polynomialFunctions V n

theorem exponentPolynomialIntegral : ExponentPolynomialIntegralStatement := by
  intro V Ω _ _ _ _ n f μ hf hi
  let : FiniteDimensional ℂ (polynomialFunctions V n) := finiteDimensional_polynomialFunctions n
  exact Langlands.Archimedean.InductionStages.integral_mem μ _ (w := f) hf hi

end Integration

end Langlands.Global
