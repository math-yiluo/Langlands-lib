import Langlands.Representation.Archimedean.RealBlockFrobeniusMap
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Choose.Bounds

/-! # Compact derivative estimates for real block Fourier multipliers -/

noncomputable section

open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealBlockFourierDecay

open RealBlockRotation RealBlockDerivative RealBlockFrobeniusMap RealBlockFourierFinite
open RealBlockMultiplier Langlands.LocalFactor.Archimedean

variable {n p : ℕ}

local notation "G" => Langlands.GeneralLinear n ℝ
local notation "M" => Matrix (Fin n) (Fin n) ℝ
local notation "K" => unitaryCompact ℝ n
local notation "D" => rightDerivative (matrixModel ℝ n)

/-- The right matrix direction corresponding to the left block rotation at `g`. -/
def rotationDirection (n p : ℕ) (g : Langlands.GeneralLinear n ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  g⁻¹.val * rotationGenerator n p * g.val

private theorem hasDerivAt_rotation (hp : p + 1 < n) {f : G → ℂ}
    (hf : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f) (g : G) (θ : ℝ) :
    HasDerivAt (fun t => f (blockRotation n p t * g))
      (D (rotationDirection n p g) f (blockRotation n p θ * g)) θ := by
  refine (hasDerivAt_blockRotation_mul hp hf g θ).congr_deriv ?_
  rw [rotDeriv, rightDerivative_eq_fderiv hf]
  have hcomm : Commute (rotationGenerator n p) (blockRotation n p θ).val := by
    rw [blockRotation_val]
    exact ((Commute.refl (rotationGenerator n p)).smul_right θ).exp_right
  have hdir : (blockRotation n p θ * g).val * rotationDirection n p g =
      rotationGenerator n p * (blockRotation n p θ * g).val := by
    simp only [Units.val_mul, rotationDirection, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc g.val, show g.val * g⁻¹.val = 1 from g.val_inv, one_mul,
      ← Matrix.mul_assoc, ← hcomm.eq, Matrix.mul_assoc]
  rw [hdir]

private def angularCharacter (j : ℤ) (θ : ℝ) : ℂ :=
  Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I))

private theorem angularCharacter_norm (j : ℤ) (θ : ℝ) : ‖angularCharacter j θ‖ = 1 := by
  unfold angularCharacter
  rw [show -((j : ℂ) * (θ : ℂ) * Complex.I) =
    (((-(j : ℝ) * θ : ℝ) : ℂ) * Complex.I) by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private theorem angularCharacter_two_pi (j : ℤ) : angularCharacter j (2 * Real.pi) = 1 := by
  unfold angularCharacter
  rw [show -((j : ℂ) * ((2 * Real.pi : ℝ) : ℂ) * Complex.I) =
    (((-j : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I _

private theorem blockFourierCoefficient_derivative (hp : p + 1 < n) {f : G → ℂ}
    (hf : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f) (g : G) (j : ℤ) :
    blockFourierCoefficient n p j (D (rotationDirection n p g) f) g =
      ((j : ℂ) * Complex.I) * blockFourierCoefficient n p j f g := by
  let E := angularCharacter j
  let F : ℝ → ℂ := fun θ => f (blockRotation n p θ * g)
  let F' : ℝ → ℂ := fun θ => D (rotationDirection n p g) f (blockRotation n p θ * g)
  let z : ℂ := (j : ℂ) * Complex.I
  have hE : Continuous E := by unfold E angularCharacter; fun_prop
  have hF : Continuous F := hf.continuous.comp ((continuous_blockRotation n p).mul continuous_const)
  have hF' : Continuous F' := (contMDiff_rightDerivative hf _).continuous.comp
    ((continuous_blockRotation n p).mul continuous_const)
  have he (θ : ℝ) : HasDerivAt E (E θ * (-z)) θ := by
    have h := ((((hasDerivAt_id θ).ofReal_comp).const_mul (j : ℂ)).mul_const Complex.I).neg
    exact (h.congr_deriv (by simp [z])).cexp
  have hd (θ : ℝ) : HasDerivAt F (F' θ) θ := hasDerivAt_rotation hp hf g θ
  have hE0 : E 0 = 1 := by simp [E, angularCharacter]
  have hE2 : E (2 * Real.pi) = 1 := angularCharacter_two_pi j
  have hF2 : F (2 * Real.pi) = F 0 := by
    dsimp [F]
    rw [blockRotation_two_pi hp, blockRotation_zero]
  change (∫ θ in (0 : ℝ)..2 * Real.pi, F' θ * E θ) =
    z * (∫ θ in (0 : ℝ)..2 * Real.pi, F θ * E θ)
  simp only [mul_comm (F' _) (E _)]
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun θ _ => he θ) (fun θ _ => hd θ)
    ((hE.mul continuous_const).intervalIntegrable _ _) (hF'.intervalIntegrable _ _), hE0, hE2,
    hF2, one_mul, sub_self, zero_sub]
  have heq : (fun θ => E θ * (-z) * F θ) = fun θ => (-z) * (F θ * E θ) := by
    funext θ
    ring
  rw [heq, intervalIntegral.integral_const_mul, neg_mul, neg_neg]

private theorem smooth_iterate (X : M) {f : G → ℂ}
    (hf : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f) (m : ℕ) :
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ ((D X)^[m] f) := by
  induction m with
  | zero => exact hf
  | succ d ih => rw [Function.iterate_succ_apply']; exact contMDiff_rightDerivative ih X

/-- Repeated differentiation along the block rotation multiplies the coefficient by
`(ij)^m`. -/
theorem blockFourierCoefficient_iterate (hp : p + 1 < n) {f : G → ℂ}
    (hf : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f) (g : G) (j : ℤ) (m : ℕ) :
    blockFourierCoefficient n p j ((D (rotationDirection n p g))^[m] f) g =
      ((j : ℂ) * Complex.I) ^ m * blockFourierCoefficient n p j f g := by
  induction m with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply', blockFourierCoefficient_derivative hp
      (smooth_iterate _ hf _), ih, pow_succ', ← mul_assoc]

/-- The uniform pointwise bound for one block Fourier coefficient. -/
theorem norm_blockFourierCoefficient_le {f : G → ℂ} {g : G} (hg : g ∈ K) (j : ℤ) {A : ℝ}
    (hA : ∀ k ∈ K, ‖f k‖ ≤ A) : ‖blockFourierCoefficient n p j f g‖ ≤ (2 * Real.pi) * A := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 2 * Real.pi)
    (f := fun θ => f (blockRotation n p θ * g) * angularCharacter j θ) (C := A)
    (fun θ _ => by
      rw [norm_mul, angularCharacter_norm, mul_one]
      exact hA _ ((unitaryCompact ℝ n).mul_mem (blockRotation_mem_unitaryCompact n p θ) hg))
  rw [sub_zero, abs_of_pos (by positivity : 0 < 2 * Real.pi), mul_comm A] at h
  exact h

/-- Differentiation in the compact rotation gives polynomial decay of the Fourier
coefficients, uniformly wherever the stated compact derivative is bounded. -/
theorem norm_blockFourierCoefficient_mul_pow_le (hp : p + 1 < n) {f : G → ℂ}
    (hf : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f) {g : G} (hg : g ∈ K)
    (j : ℤ) (m : ℕ) {A : ℝ} (hA : ∀ k ∈ K,
      ‖((D (rotationDirection n p g))^[m] f) k‖ ≤ A) :
    |(j : ℝ)| ^ m * ‖blockFourierCoefficient n p j f g‖ ≤ (2 * Real.pi) * A := by
  have h := norm_blockFourierCoefficient_le (p := p) hg j hA
  rw [blockFourierCoefficient_iterate hp hf g j m, norm_mul, norm_pow, norm_mul,
    Complex.norm_I, mul_one, Complex.norm_intCast] at h
  exact h

/-- The binomial tail multiplier is bounded by a power of the mode plus a fixed constant. -/
theorem norm_tailMultiplier_le (ℓ : ℕ) (ε : ℤ) {σ : ℂ} (hσ : ‖σ‖ = 1) (j : ℤ) :
    ‖tailMultiplier ℓ ε σ j‖ ≤
      ((ℓ + ε.toNat + 1 : ℕ) : ℝ) ^ ℓ * (max 1 |(j : ℝ)|) ^ ℓ := by
  have heq : ‖tailMultiplier ℓ ε σ j‖ = ‖tailSeq ℓ ε (j.natAbs / 2)‖ := by
    by_cases hj : 0 ≤ j
    · rw [tailMultiplier, extend_of_nonneg hj]
    · rw [tailMultiplier, extend_of_neg (lt_of_not_ge hj), norm_mul, hσ, one_mul]
  rw [heq, tailSeq, Complex.norm_natCast, ← mul_pow]
  have hb : j.natAbs / 2 + (ℓ - 1 + ε.toNat) / 2 ≤
      (ℓ + ε.toNat + 1) * max 1 j.natAbs := by
    have h₁ : j.natAbs ≤ max 1 j.natAbs := le_max_right _ _
    have h₂ : ℓ + ε.toNat ≤ (ℓ + ε.toNat) * max 1 j.natAbs :=
      Nat.le_mul_of_pos_right _ (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
    rw [Nat.add_mul, one_mul]
    omega
  have hAbs : |(j : ℝ)| = (j.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  rw [hAbs]
  exact (by exact_mod_cast Nat.choose_le_pow (j.natAbs / 2 + (ℓ - 1 + ε.toNat) / 2) ℓ :
    (((j.natAbs / 2 + (ℓ - 1 + ε.toNat) / 2).choose ℓ : ℕ) : ℝ) ≤
      (↑(j.natAbs / 2 + (ℓ - 1 + ε.toNat) / 2) : ℝ) ^ ℓ).trans
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hb) _)

private def modeMajorant (j : ℤ) : ℝ := if j = 0 then 1 else 1 / (j : ℝ) ^ 2

private theorem modeMajorant_nonneg (j : ℤ) : 0 ≤ modeMajorant j := by
  by_cases h : j = 0
  · simp [modeMajorant, h]
  · simp only [modeMajorant, h, ite_false]
    positivity

private theorem summable_modeMajorant : Summable modeMajorant :=
  (Real.summable_one_div_int_pow.mpr (by decide : 1 < 2)).congr_cofinite <|
    (Filter.eventually_cofinite_ne (0 : ℤ)).mono fun j hj => by simp [modeMajorant, hj]

private theorem one_le_abs_mode {j : ℤ} (hj : j ≠ 0) : 1 ≤ |(j : ℝ)| := by
  rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  have h : 1 ≤ j.natAbs := Int.natAbs_pos.mpr hj
  exact_mod_cast h

private theorem norm_weightedCoefficient_le {f : G → ℂ} {μ : ℤ → ℂ} (d : ℕ)
    (hp : p + 1 < n) (hf : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f) {g : G} (hg : g ∈ K)
    {C A : ℝ} (hC : 0 ≤ C) (hμ : ∀ j, ‖μ j‖ ≤ C * (max 1 |(j : ℝ)|) ^ d)
    (h₀ : ∀ k ∈ K, ‖f k‖ ≤ A)
    (hA : ∀ k ∈ K, ‖((D (rotationDirection n p g))^[d + 2] f) k‖ ≤ A)
    (j : ℤ) :
    ‖μ j * blockFourierCoefficient n p j f g‖ ≤ C * ((2 * Real.pi) * A) * modeMajorant j := by
  rw [norm_mul]
  by_cases hj : j = 0
  · subst j
    have hμ₀ : ‖μ 0‖ ≤ C := by simpa using hμ 0
    have hq : modeMajorant 0 = 1 := by simp [modeMajorant]
    simpa only [hq, mul_one] using
      mul_le_mul hμ₀ (norm_blockFourierCoefficient_le (p := p) hg 0 h₀) (norm_nonneg _) hC
  · have hb := norm_blockFourierCoefficient_mul_pow_le hp hf hg j (d + 2) hA
    have hpos : 0 < |(j : ℝ)| := zero_lt_one.trans_le (one_le_abs_mode hj)
    have hq : modeMajorant j = (|(j : ℝ)| ^ 2)⁻¹ := by
      simp only [modeMajorant, hj, ite_false, one_div, sq_abs]
    calc
      _ ≤ (C * |(j : ℝ)| ^ d) * ‖blockFourierCoefficient n p j f g‖ := by
        exact mul_le_mul_of_nonneg_right
          (by simpa only [max_eq_right (one_le_abs_mode hj)] using hμ j) (norm_nonneg _)
      _ = C * (|(j : ℝ)| ^ (d + 2) * ‖blockFourierCoefficient n p j f g‖) * modeMajorant j := by
        rw [hq, pow_add]
        field_simp [hpos.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hC) (modeMajorant_nonneg j)

/-- A polynomially bounded block multiplier applied to a compact-finite vector
is bounded on the compact group by its order-zero and order-`d + 2` rotation suprema. -/
theorem norm_blockFrobMap_le {ds es : List RealBlock} {ε : ℤ} {σ : ℂ} {μ : ℤ → ℂ}
    (h : IsBlockFrobData n ds es p ε σ μ) (d : ℕ) {C : ℝ}
    (hC : 0 ≤ C) (hμ : ∀ j, ‖μ j‖ ≤ C * (max 1 |(j : ℝ)|) ^ d)
    (f : kFiniteFunctions (realStandardModule n ds) K) {g : G} (hg : g ∈ K)
    {A : ℝ} (h₀ : ∀ k ∈ K, ‖f.val k‖ ≤ A)
    (hA : ∀ k ∈ K, ‖((D (rotationDirection n p g))^[d + 2] f.val) k‖ ≤ A) :
    ‖(blockFrobMap h f).val g‖ ≤ C * A * ∑' j, modeMajorant j := by
  classical
  let a (j : ℤ) := μ j * blockFourierCoefficient n p j f.val g
  have hf := f.property.1.1.1
  have hsup := finite_support_blockFourierCoefficient h.lt hf.continuous f.property.2 hg
  let s := hsup.toFinset
  have has : Function.support a ⊆ ↑s := by
    intro j hj
    rw [Set.Finite.coe_toFinset]
    intro hz
    apply hj
    exact mul_eq_zero.mpr (Or.inr hz)
  have hb (j : ℤ) : ‖a j‖ ≤ C * ((2 * Real.pi) * A) * modeMajorant j :=
    norm_weightedCoefficient_le d h.lt hf hg hC hμ h₀ hA j
  have hA₀ : 0 ≤ A := (norm_nonneg _).trans (h₀ g hg)
  have hc : 0 ≤ C * ((2 * Real.pi) * A) := by positivity
  have hsum : ‖∑ j ∈ s, a j‖ ≤ (C * ((2 * Real.pi) * A)) * ∑' j, modeMajorant j := by
    calc
      _ ≤ ∑ j ∈ s, ‖a j‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ s, C * ((2 * Real.pi) * A) * modeMajorant j :=
        Finset.sum_le_sum fun j _ => hb j
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left
          (summable_modeMajorant.sum_le_tsum s (fun j _ => modeMajorant_nonneg j)) hc
  have hp : 0 < 2 * Real.pi := by positivity
  rw [blockFrobMap_apply_of_mem h f hg, finsum_eq_sum_of_support_subset a has,
    norm_mul, norm_inv]
  have hn : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_of_nonneg hp.le]
  rw [hn]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * ((C * ((2 * Real.pi) * A)) * ∑' j, modeMajorant j) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hp.le)
    _ = _ := by field_simp [hp.ne']

/-- Compact sup-norm bounds for polynomially bounded block Fourier multipliers. -/
def RealBlockFourierDecayStatement : Prop :=
  ∀ (n p d : ℕ) (ds es : List RealBlock) (ε : ℤ) (σ : ℂ) (μ : ℤ → ℂ)
    (h : IsBlockFrobData n ds es p ε σ μ) (C : ℝ), 0 ≤ C →
    (∀ j, ‖μ j‖ ≤ C * (max 1 |(j : ℝ)|) ^ d) →
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
        (g : Langlands.GeneralLinear n ℝ), g ∈ unitaryCompact ℝ n →
      ∀ A : ℝ, (∀ k ∈ unitaryCompact ℝ n, ‖f.val k‖ ≤ A) →
        (∀ k ∈ unitaryCompact ℝ n,
          ‖((rightDerivative (matrixModel ℝ n) (rotationDirection n p g))^[d + 2] f.val) k‖ ≤ A) →
        ‖(blockFrobMap h f).val g‖ ≤ B * A

theorem realBlockFourierDecay : RealBlockFourierDecayStatement := by
  intro n p d ds es ε σ μ h C hC hμ
  let B := C * ∑' j, modeMajorant j
  have hB : 0 ≤ B := mul_nonneg hC (tsum_nonneg modeMajorant_nonneg)
  refine ⟨B, hB, fun f g hg A h₀ hA => ?_⟩
  simpa only [B, mul_right_comm C] using norm_blockFrobMap_le h d hC hμ f hg h₀ hA

end Langlands.Archimedean.RealBlockFourierDecay
