import Langlands.Representation.Archimedean.WeightedPolynomialDerivative
import Langlands.Representation.Archimedean.FormalRealPolynomials

/-!
# Holomorphic derivatives of weighted functions

Let `T_j` (`j : κ`) be differentiable functions with positive real values,
`ω = ∏_j T_j^{σ_j}` and `D = ∏_j T_j`. If `φ D^N = ω P` with `φ`, `P` differentiable, then at
every point and in every direction `w` (`fderiv_weighted_apply`)
`Dφ[w] D^{N+1} = ω (Q_w P + D · DP[w] - N P · DD[w])`, `Q_w = Σ_j σ_j DT_j[w] ∏_{j' ≠ j} T_{j'}`.
The same identity holds for the complex-linear parts `wirt` of the derivatives
(`wirt_weighted_apply`).
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.RealPolynomialFunctions

open scoped ComplexConjugate

variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **The weighted derivative at a point.** -/
theorem fderiv_weighted_apply (T : κ → (ι → ℂ) → ℂ) (hTd : ∀ j, Differentiable ℝ (T j))
    (hTpos : ∀ j, IsPosReal (T j)) (σ : κ → ℂ) {φ P : (ι → ℂ) → ℂ} (hφ : Differentiable ℝ φ)
    (hPd : Differentiable ℝ P) {N : ℕ}
    (hrel : ∀ v, φ v * (∏ j, T j v) ^ N = (∏ j, T j v ^ σ j) * P v) (v w : ι → ℂ) :
    fderiv ℝ φ v w * (∏ j, T j v) ^ (N + 1) = (∏ j, T j v ^ σ j) *
      ((∑ j, σ j * fderiv ℝ (T j) v w * ∏ j' ∈ Finset.univ.erase j, T j' v) * P v +
        (∏ j, T j v) * fderiv ℝ P v w - N * P v * fderiv ℝ (fun x => ∏ j, T j x) v w) := by
  set D : (ι → ℂ) → ℂ := fun v => ∏ j, T j v
  set ω : (ι → ℂ) → ℂ := fun v => ∏ j, T j v ^ σ j
  have hDd : Differentiable ℝ D := fun x =>
    (HasFDerivAt.finsetProd (u := Finset.univ) fun j _ => ((hTd j) x).hasFDerivAt).differentiableAt
  set Q : ℂ := ∑ j, σ j * fderiv ℝ (T j) v w * ∏ j' ∈ Finset.univ.erase j, T j' v
  have hωd : ∀ x, HasFDerivAt ω (∑ j, (∏ j' ∈ Finset.univ.erase j, T j' x ^ σ j') •
      ((σ j * T j x ^ (σ j - 1)) • fderiv ℝ (T j) x)) x := by
    intro x
    have := HasFDerivAt.finsetProd (u := Finset.univ) (fun j _ =>
      hasFDerivAt_cpow_comp ((hTd j) x).hasFDerivAt ((hTpos j).mem_slitPlane x) (σ j))
    simpa [ω] using this
  have hωQ : fderiv ℝ ω v w * D v = ω v * Q := by
    rw [(hωd v).fderiv]
    simp only [FunLike.coe_sum, Finset.sum_apply, _root_.smul_apply, smul_eq_mul, Finset.sum_mul,
      Q, Finset.mul_sum, D, ω]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hTj : T j v ^ (σ j - 1) * T j v = T j v ^ σ j := by
      rw [Complex.cpow_sub _ _ ((hTpos j).ne_zero v), Complex.cpow_one,
        div_mul_cancel₀ _ ((hTpos j).ne_zero v)]
    rw [← Finset.mul_prod_erase Finset.univ (fun j => T j v) (Finset.mem_univ j),
      ← Finset.mul_prod_erase Finset.univ (fun j => T j v ^ σ j) (Finset.mem_univ j)]
    rw [← hTj]
    ring
  have hωdiff : Differentiable ℝ ω := fun x => (hωd x).differentiableAt
  have hrel' : (fun v => φ v * D v ^ N) = fun v => ω v * P v := funext hrel
  have hderiv : fderiv ℝ φ v w * D v ^ N + φ v * ((N : ℂ) * D v ^ (N - 1) * fderiv ℝ D v w) =
      fderiv ℝ ω v w * P v + ω v * fderiv ℝ P v w := by
    have h1 : fderiv ℝ (fun v => φ v * D v ^ N) v w = fderiv ℝ (fun v => ω v * P v) v w := by
      rw [hrel']
    rw [fderiv_fun_mul (hφ v) (show DifferentiableAt ℝ (fun x => D x ^ N) v from (hDd v).pow N),
      fderiv_fun_pow N (hDd v), fderiv_fun_mul (hωdiff v) (hPd v)] at h1
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, nsmul_eq_mul] at h1
    linear_combination h1
  have hrv : φ v * D v ^ N = ω v * P v := hrel v
  change fderiv ℝ φ v w * D v ^ (N + 1) = ω v * (Q * P v + D v * fderiv ℝ P v w -
    N * P v * fderiv ℝ D v w)
  rcases N with _ | N
  · simp only [pow_zero, mul_one, Nat.cast_zero, zero_mul, zero_add, mul_zero, add_zero,
      sub_zero, pow_one] at hderiv hrv ⊢
    linear_combination (D v) * hderiv + (P v) * hωQ
  · simp only [Nat.add_sub_cancel] at hderiv
    push_cast at hderiv ⊢
    linear_combination (D v) * hderiv + (P v) * hωQ - ((N : ℂ) + 1) * fderiv ℝ D v w * hrv

/-- **The weighted holomorphic derivative at a point.** -/
theorem wirt_weighted_apply (T : κ → (ι → ℂ) → ℂ) (hTd : ∀ j, Differentiable ℝ (T j))
    (hTpos : ∀ j, IsPosReal (T j)) (σ : κ → ℂ) {φ P : (ι → ℂ) → ℂ} (hφ : Differentiable ℝ φ)
    (hPd : Differentiable ℝ P) {N : ℕ}
    (hrel : ∀ v, φ v * (∏ j, T j v) ^ N = (∏ j, T j v ^ σ j) * P v) (v w : ι → ℂ) :
    wirt φ v w * (∏ j, T j v) ^ (N + 1) = (∏ j, T j v ^ σ j) *
      ((∑ j, σ j * wirt (T j) v w * ∏ j' ∈ Finset.univ.erase j, T j' v) * P v +
        (∏ j, T j v) * wirt P v w - N * P v * wirt (fun x => ∏ j, T j x) v w) := by
  have h1 := fderiv_weighted_apply T hTd hTpos σ hφ hPd hrel v w
  have h2 := fderiv_weighted_apply T hTd hTpos σ hφ hPd hrel v (Complex.I • w)
  simp only [wirt]
  have e : ∑ j, σ j * ((2 : ℂ)⁻¹ * (fderiv ℝ (T j) v w - Complex.I *
      fderiv ℝ (T j) v (Complex.I • w))) * ∏ j' ∈ Finset.univ.erase j, T j' v =
      (2 : ℂ)⁻¹ * ((∑ j, σ j * fderiv ℝ (T j) v w * ∏ j' ∈ Finset.univ.erase j, T j' v) -
        Complex.I * ∑ j, σ j * fderiv ℝ (T j) v (Complex.I • w) *
          ∏ j' ∈ Finset.univ.erase j, T j' v) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  linear_combination (2 : ℂ)⁻¹ * h1 - (2 : ℂ)⁻¹ * Complex.I * h2

end Langlands.Archimedean.RealPolynomialFunctions
