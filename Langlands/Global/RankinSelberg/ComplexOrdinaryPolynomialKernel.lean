import Langlands.Global.RankinSelberg.OrdinarySemilocalNormalization
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Linear spanning of integrable polynomial normalizations -/

noncomputable section

open MeasureTheory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

variable {X : Type*} [MeasurableSpace X]

/-- Kernels on the given measure space whose integrals converge on a right
half-plane and equal a polynomial times the prescribed factor there. -/
def polynomialOrdinaryKernels (μ : Measure X) (L : ℂ → ℂ) : Submodule ℂ (ℂ → X → ℂ) where
  carrier := {K | ∃ (P : Polynomial ℂ) (σ : ℝ), ∀ s : ℂ, σ < s.re →
    Integrable (K s) μ ∧ (∫ x, K s x ∂μ) = P.eval s * L s}
  zero_mem' := ⟨0, 0, fun s _ => by simp⟩
  add_mem' := by
    rintro K J ⟨P, σ, hP⟩ ⟨Q, τ, hQ⟩
    refine ⟨P + Q, max σ τ, fun s hs => ?_⟩
    obtain ⟨hK, hKe⟩ := hP s ((le_max_left _ _).trans_lt hs)
    obtain ⟨hJ, hJe⟩ := hQ s ((le_max_right _ _).trans_lt hs)
    refine ⟨hK.add hJ, ?_⟩
    simp only [Pi.add_def, integral_add hK hJ, hKe, hJe, Polynomial.eval_add, add_mul]
  smul_mem' := by
    rintro c K ⟨P, σ, hP⟩
    refine ⟨Polynomial.C c * P, σ, fun s hs => ?_⟩
    obtain ⟨hK, hKe⟩ := hP s hs
    refine ⟨hK.const_mul c, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, integral_const_mul, hKe, Polynomial.eval_mul,
      Polynomial.eval_C, mul_assoc]

/-- An integrable kernel with a polynomial normalization on a right half-plane
has an ordinary entire normalization given by that polynomial. -/
theorem exists_ordinaryPolynomialNormalization_of_mem {μ : Measure X} {L : ℂ → ℂ} {K : ℂ → X → ℂ}
    (hK : K ∈ polynomialOrdinaryKernels μ L) :
    ∃ (N : OrdinaryIntegralNormalization (fun s => ∫ x, K s x ∂μ) L) (P : Polynomial ℂ),
      N.value = P.eval := by
  obtain ⟨P, σ, hP⟩ := hK
  exact ⟨⟨P.eval, fun s _ => P.differentiable.analyticAt s, σ, fun s hs => (hP s hs).2⟩, P, rfl⟩

/-- A polynomial ordinary normalization and right-half-plane integrability put the
kernel in the polynomial subspace. -/
theorem mem_polynomialOrdinaryKernels_of_normalization {μ : Measure X} {L : ℂ → ℂ} {K : ℂ → X → ℂ}
    (N : OrdinaryIntegralNormalization (fun s => ∫ x, K s x ∂μ) L) (P : Polynomial ℂ)
    (hP : N.value = P.eval) (hI : ∃ τ : ℝ, ∀ s : ℂ, τ < s.re → Integrable (K s) μ) :
    K ∈ polynomialOrdinaryKernels μ L := by
  obtain ⟨τ, hτ⟩ := hI
  obtain ⟨σ, hσ⟩ := N.eq_on_right
  refine ⟨P, max σ τ, fun s hs => ⟨hτ s ((le_max_right _ _).trans_lt hs), ?_⟩⟩
  rw [← congrFun hP s]
  exact hσ s ((le_max_left _ _).trans_lt hs)

end Langlands.Global.RankinSelbergGlobal
