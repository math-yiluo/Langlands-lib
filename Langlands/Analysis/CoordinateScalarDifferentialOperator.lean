import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Basis.Defs

/-! # Coordinate scalar differential data and real-covector symbols -/

noncomputable section
universe v
set_option autoImplicit false

namespace Langlands.Analysis

/-- Actual finite coordinate coefficients on the existing real normed domain.
No regularity, ellipticity or analytic-solution certificate is bundled. -/
structure CoordinateScalarOperator (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d r : ℕ) where
  /-- A finite real basis of actual vectors of `E`; the norm of `E` is unchanged. -/
  basis : Module.Basis (Fin d) ℝ E
  /-- The complex coefficient of the ordered derivative word `w` of length `k ≤ r`. -/
  coefficient : (k : Fin (r + 1)) → (Fin k.val → Fin d) → E → ℂ

namespace CoordinateScalarOperator

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] {d r : ℕ}

/-- The full finite-order expression, evaluated using real iterated Frechet derivatives. -/
def action (D : CoordinateScalarOperator E d r) (F : E → ℂ) (x : E) : ℂ :=
  ∑ k : Fin (r + 1), ∑ w : Fin k.val → Fin d,
    D.coefficient k w x * iteratedFDeriv ℝ k.val F x (fun j => D.basis (w j))

/-- Highest-order symbol on real continuous covectors, without a factor of `i`. -/
def principalSymbol (D : CoordinateScalarOperator E d r) (x : E) (ξ : E →L[ℝ] ℝ) : ℂ :=
  ∑ w : Fin r → Fin d, D.coefficient (Fin.last r) w x *
    ∏ j : Fin r, (ξ (D.basis (w j)) : ℂ)

/-- Real analyticity of every actual scalar coefficient near every point of the given set. -/
def AnalyticCoefficientsOn (D : CoordinateScalarOperator E d r) (S : Set E) : Prop :=
  ∀ (k : Fin (r + 1)) (w : Fin k.val → Fin d),
    AnalyticOnNhd ℝ (D.coefficient k w) S

/-- Nonvanishing of the actual highest-order symbol on every nonzero real covector. -/
def IsEllipticOn (D : CoordinateScalarOperator E d r) (S : Set E) : Prop :=
  ∀ x ∈ S, ∀ ξ : E →L[ℝ] ℝ, ξ ≠ 0 → D.principalSymbol x ξ ≠ 0

/-- One positive homogeneous symbol bound in the original continuous-dual operator norm. -/
def IsUniformlyEllipticOn (D : CoordinateScalarOperator E d r) (S : Set E) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x ∈ S, ∀ ξ : E →L[ℝ] ℝ,
    c * ‖ξ‖ ^ r ≤ ‖D.principalSymbol x ξ‖

/-- The constructed symbol is homogeneous of the specified highest order on real covectors. -/
theorem principalSymbol_smul (D : CoordinateScalarOperator E d r) (x : E) (c : ℝ)
    (ξ : E →L[ℝ] ℝ) :
    D.principalSymbol x (c • ξ) = (c : ℂ) ^ r * D.principalSymbol x ξ := by
  simp only [principalSymbol, smul_apply, smul_eq_mul, Complex.ofReal_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  ring

/-- The uniform homogeneous lower bound implies pointwise ellipticity. -/
theorem IsUniformlyEllipticOn.isEllipticOn {D : CoordinateScalarOperator E d r} {S : Set E}
    (h : D.IsUniformlyEllipticOn S) : D.IsEllipticOn S := by
  obtain ⟨c, hc, hbound⟩ := h
  intro x hx ξ hξ hzero
  have hle := hbound x hx ξ
  rw [hzero, norm_zero] at hle
  have hpos : 0 < c * ‖ξ‖ ^ r := mul_pos hc (pow_pos (norm_pos_iff.mpr hξ) r)
  linarith

/-- Coefficient analyticity restricts to subsets. -/
theorem AnalyticCoefficientsOn.mono {D : CoordinateScalarOperator E d r} {S T : Set E}
    (h : D.AnalyticCoefficientsOn S) (hTS : T ⊆ S) : D.AnalyticCoefficientsOn T :=
  fun k w => (h k w).mono hTS

/-- Ellipticity restricts to subsets. -/
theorem IsEllipticOn.mono {D : CoordinateScalarOperator E d r} {S T : Set E}
    (h : D.IsEllipticOn S) (hTS : T ⊆ S) : D.IsEllipticOn T :=
  fun x hx => h x (hTS hx)

/-- Uniform ellipticity restricts to subsets with the same constant. -/
theorem IsUniformlyEllipticOn.mono {D : CoordinateScalarOperator E d r} {S T : Set E}
    (h : D.IsUniformlyEllipticOn S) (hTS : T ⊆ S) : D.IsUniformlyEllipticOn T := by
  obtain ⟨c, hc, hbound⟩ := h
  exact ⟨c, hc, fun x hx => hbound x (hTS hx)⟩

end CoordinateScalarOperator
end Langlands.Analysis
