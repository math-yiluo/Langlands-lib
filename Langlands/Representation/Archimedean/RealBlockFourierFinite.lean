import Langlands.Representation.Archimedean.RealBlockRotation
import Langlands.Representation.Archimedean.OrthogonalFinitePolynomial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fourier coefficients along a block rotation

Facts about the Fourier coefficients `Φ_j f (g) = ∫₀^{2π} f(r_p(θ) g) e^{-ijθ} dθ`
(`blockFourierCoefficient N p j f g`) along the rotations `r_p(θ)` in the coordinates `p, p + 1`
of `GL_N(ℝ)`, for `p + 1 < N`:

* left rotation multiplies `Φ_j` by `e^{ijφ}`;
* for a continuous right `O(N)`-finite function, `θ ↦ f(r_p(θ) g)` is a trigonometric polynomial
  of degree bounded uniformly in `g ∈ O(N)`. So only finitely many `Φ_j f (g)` are nonzero, and
  `f(g) = (2π)⁻¹ Σ_j Φ_j f (g)`;
* for a principal series function, `Φ_j` vanishes unless `(-1)^j = χ_p(-1) χ_{p+1}(-1)`, and the
  sign matrices `s_i` act on `Φ_j` through `χ_i(-1)`, reversing `j` when `i ∈ {p, p + 1}`;
* Fourier coefficients along disjoint blocks commute.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

namespace RealBlockFourierFinite

open RealBlockRotation

/-! ## Exponentials and Fourier coefficients on `[0, 2π]` -/

/-- The exponential `θ ↦ e^{ikθ}`. -/
def expMode (k : ℤ) (θ : ℝ) : ℂ :=
  Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I)

/-- The `k`-th Fourier coefficient `∫₀^{2π} F(θ) e^{-ikθ} dθ` of a function `F` on `ℝ`. -/
def coeff (k : ℤ) (F : ℝ → ℂ) : ℂ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi, F θ * Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I))

theorem blockFourierCoefficient_eq_coeff (N p : ℕ) (k : ℤ)
    (f : Langlands.GeneralLinear N ℝ → ℂ) (g : Langlands.GeneralLinear N ℝ) :
    blockFourierCoefficient N p k f g = coeff k (fun θ => f (blockRotation N p θ * g)) :=
  rfl

theorem continuous_expMode (k : ℤ) : Continuous (expMode k) := by
  unfold expMode
  fun_prop

theorem expMode_add (j k : ℤ) : expMode j * expMode k = expMode (j + k) := by
  funext θ
  simp only [expMode, Pi.mul_apply, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem expMode_zero_left (θ : ℝ) : expMode 0 θ = 1 := by
  simp [expMode]

/-- `∫₀^{2π} e^{imθ} dθ` is `2π` for `m = 0` and `0` otherwise. -/
theorem integral_exp_int_mul (m : ℤ) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I) =
      if m = 0 then 2 * (Real.pi : ℂ) else 0 := by
  split_ifs with hm
  · subst hm
    simp
  · have hc : (m : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hm) Complex.I_ne_zero
    have hrw : ∀ θ : ℝ, (m : ℂ) * (θ : ℂ) * Complex.I = (m * Complex.I) * θ := fun θ => by ring
    simp_rw [hrw]
    rw [integral_exp_mul_complex hc]
    have h2 : (m : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ) = m * (2 * Real.pi * Complex.I) := by
      push_cast
      ring
    rw [h2, Complex.exp_int_mul_two_pi_mul_I]
    simp

/-- Orthogonality: `∫₀^{2π} e^{ikθ} e^{-ijθ} dθ = 2π δ_{jk}`. -/
theorem coeff_expMode (j k : ℤ) :
    coeff j (expMode k) = if k = j then 2 * (Real.pi : ℂ) else 0 := by
  unfold coeff expMode
  have h : ∀ θ : ℝ, Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I) *
      Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) =
        Complex.exp (((k - j : ℤ) : ℂ) * (θ : ℂ) * Complex.I) := by
    intro θ
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [h, integral_exp_int_mul, sub_eq_zero]

theorem intervalIntegrable_coeff {F : ℝ → ℂ} (hF : Continuous F) (k : ℤ) (a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => F θ * Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)))
      MeasureTheory.volume a b :=
  (hF.mul (by fun_prop)).intervalIntegrable a b

theorem coeff_add {F G : ℝ → ℂ} (hF : Continuous F) (hG : Continuous G) (k : ℤ) :
    coeff k (F + G) = coeff k F + coeff k G := by
  unfold coeff
  simp only [Pi.add_apply, add_mul]
  exact intervalIntegral.integral_add (intervalIntegrable_coeff hF k _ _)
    (intervalIntegrable_coeff hG k _ _)

theorem coeff_smul (c : ℂ) (F : ℝ → ℂ) (k : ℤ) : coeff k (c • F) = c * coeff k F := by
  unfold coeff
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact intervalIntegral.integral_const_mul c _

theorem coeff_zero_fun (k : ℤ) : coeff k 0 = 0 := by
  simp [coeff]

theorem periodic_exp_neg (k : ℤ) :
    Function.Periodic (fun θ : ℝ => Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)))
      (2 * Real.pi) := by
  intro θ
  have h : -((k : ℂ) * ((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
      -((k : ℂ) * (θ : ℂ) * Complex.I) + ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  simp only
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Shifting the variable of a `2π`-periodic function by `φ` multiplies its `k`-th Fourier
coefficient by `e^{ikφ}`. -/
theorem coeff_comp_add {F : ℝ → ℂ} (hF : Function.Periodic F (2 * Real.pi)) (k : ℤ) (φ : ℝ) :
    coeff k (fun θ => F (θ + φ)) = expMode k φ * coeff k F := by
  unfold coeff
  have h : ∀ θ : ℝ, F (θ + φ) * Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)) =
      expMode k φ * (F (θ + φ) * Complex.exp (-((k : ℂ) * ((θ + φ : ℝ) : ℂ) * Complex.I))) := by
    intro θ
    rw [expMode, mul_left_comm, mul_assoc, ← Complex.exp_add]
    congr 3
    push_cast
    ring
  have hP : Function.Periodic (fun x : ℝ => F x * Complex.exp (-((k : ℂ) * (x : ℂ) * Complex.I)))
      (2 * Real.pi) := hF.mul (periodic_exp_neg k)
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_add_right
      (fun x : ℝ => F x * Complex.exp (-((k : ℂ) * (x : ℂ) * Complex.I))) φ,
    zero_add, add_comm (2 * Real.pi) φ, hP.intervalIntegral_add_eq φ 0, zero_add]

/-- Reflecting the variable of a `2π`-periodic function reverses its Fourier coefficients. -/
theorem coeff_comp_neg {F : ℝ → ℂ} (hF : Function.Periodic F (2 * Real.pi)) (k : ℤ) :
    coeff k (fun θ => F (-θ)) = coeff (-k) F := by
  unfold coeff
  set G : ℝ → ℂ := fun x => F x * Complex.exp (-(((-k : ℤ) : ℂ) * (x : ℂ) * Complex.I)) with hG
  have hP : Function.Periodic G (2 * Real.pi) := hF.mul (periodic_exp_neg (-k))
  have h : (fun θ : ℝ => F (-θ) * Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I))) =
      fun θ => G (-θ) := by
    funext θ
    rw [hG]
    congr 2
    push_cast
    ring
  rw [h, intervalIntegral.integral_comp_neg G, neg_zero]
  have := hP.intervalIntegral_add_eq (-(2 * Real.pi)) 0
  rw [neg_add_cancel, zero_add] at this
  exact this

/-! ## Trigonometric polynomials -/

/-- The trigonometric polynomials of degree at most `D`: the span of the `e^{ikθ}`, `|k| ≤ D`. -/
def trigPoly (D : ℕ) : Submodule ℂ (ℝ → ℂ) :=
  Submodule.span ℂ (expMode '' {k : ℤ | |k| ≤ D})

theorem expMode_mem_trigPoly {D : ℕ} {k : ℤ} (hk : |k| ≤ D) : expMode k ∈ trigPoly D :=
  Submodule.subset_span ⟨k, hk, rfl⟩

theorem trigPoly_mono {D D' : ℕ} (h : D ≤ D') : trigPoly D ≤ trigPoly D' :=
  Submodule.span_mono (Set.image_mono fun k (hk : |k| ≤ D) =>
    (show |k| ≤ D' from hk.trans (by exact_mod_cast h)))

theorem const_mem_trigPoly (c : ℂ) : (fun _ : ℝ => c) ∈ trigPoly 0 := by
  have h : (fun _ : ℝ => c) = c • expMode 0 := by
    funext θ
    simp [expMode_zero_left]
  rw [h]
  exact Submodule.smul_mem _ _ (expMode_mem_trigPoly (by simp))

theorem cos_mem_trigPoly : (fun θ : ℝ => (Real.cos θ : ℂ)) ∈ trigPoly 1 := by
  have h : (fun θ : ℝ => (Real.cos θ : ℂ)) =
      (1 / 2 : ℂ) • expMode 1 + (1 / 2 : ℂ) • expMode (-1) := by
    funext θ
    simp only [Complex.ofReal_cos, Complex.cos, expMode, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Int.cast_one, Int.cast_neg]
    ring_nf
  rw [h]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (expMode_mem_trigPoly (by simp)))
    (Submodule.smul_mem _ _ (expMode_mem_trigPoly (by simp)))

theorem sin_mem_trigPoly : (fun θ : ℝ => (Real.sin θ : ℂ)) ∈ trigPoly 1 := by
  have h : (fun θ : ℝ => (Real.sin θ : ℂ)) =
      (-Complex.I / 2) • expMode 1 + (Complex.I / 2) • expMode (-1) := by
    funext θ
    simp only [Complex.ofReal_sin, Complex.sin, expMode, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Int.cast_one, Int.cast_neg]
    ring_nf
  rw [h]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (expMode_mem_trigPoly (by simp)))
    (Submodule.smul_mem _ _ (expMode_mem_trigPoly (by simp)))

/-- The functions `a + (cos θ - 1) b + (sin θ) c` are trigonometric polynomials of degree `1`. -/
theorem affine_mem_trigPoly (a b c : ℂ) :
    (fun θ : ℝ => a + ((Real.cos θ : ℂ) - 1) * b + (Real.sin θ : ℂ) * c) ∈ trigPoly 1 := by
  have h : (fun θ : ℝ => a + ((Real.cos θ : ℂ) - 1) * b + (Real.sin θ : ℂ) * c) =
      (fun _ : ℝ => a - b) + b • (fun θ : ℝ => (Real.cos θ : ℂ)) +
        c • (fun θ : ℝ => (Real.sin θ : ℂ)) := by
    funext θ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h]
  exact Submodule.add_mem _ (Submodule.add_mem _ (trigPoly_mono zero_le_one (const_mem_trigPoly _))
    (Submodule.smul_mem _ _ cos_mem_trigPoly)) (Submodule.smul_mem _ _ sin_mem_trigPoly)

theorem mul_mem_trigPoly {a b : ℕ} {F G : ℝ → ℂ} (hF : F ∈ trigPoly a) (hG : G ∈ trigPoly b) :
    F * G ∈ trigPoly (a + b) := by
  have h := Submodule.mul_mem_mul hF hG
  rw [trigPoly, trigPoly, Submodule.span_mul_span] at h
  refine Submodule.span_le.mpr ?_ h
  rintro _ ⟨_, ⟨j, hj, rfl⟩, _, ⟨k, hk, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨j + k, ?_, (expMode_add j k).symm⟩
  have hj' : |j| ≤ (a : ℤ) := hj
  have hk' : |k| ≤ (b : ℤ) := hk
  show |j + k| ≤ ((a + b : ℕ) : ℤ)
  push_cast
  exact (abs_add_le j k).trans (add_le_add hj' hk')

/-- A polynomial in trigonometric polynomials of degree `1` is a trigonometric polynomial, of a
degree that depends only on the polynomial. -/
theorem exists_eval_mem_trigPoly {σ : Type*} (P : MvPolynomial σ ℂ) :
    ∃ D : ℕ, ∀ x : σ → ℝ → ℂ, (∀ i, x i ∈ trigPoly 1) →
      (fun θ => MvPolynomial.eval (fun i => x i θ) P) ∈ trigPoly D := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      exact ⟨0, fun x _ => by simpa using const_mem_trigPoly a⟩
  | add P Q hP hQ =>
      obtain ⟨D₁, h₁⟩ := hP
      obtain ⟨D₂, h₂⟩ := hQ
      refine ⟨max D₁ D₂, fun x hx => ?_⟩
      simp only [map_add]
      exact Submodule.add_mem _ (trigPoly_mono (le_max_left _ _) (h₁ x hx))
        (trigPoly_mono (le_max_right _ _) (h₂ x hx))
  | mul_X P i hP =>
      obtain ⟨D, hD⟩ := hP
      refine ⟨D + 1, fun x hx => ?_⟩
      simp only [map_mul, MvPolynomial.eval_X]
      exact mul_mem_trigPoly (hD x hx) (hx i)

theorem continuous_of_mem_trigPoly {D : ℕ} {F : ℝ → ℂ} (hF : F ∈ trigPoly D) : Continuous F := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, _, rfl⟩ := hx
      exact continuous_expMode k
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.const_smul c

/-- The Fourier coefficients of a trigonometric polynomial of degree `≤ D` vanish beyond `D`. -/
theorem coeff_eq_zero_of_mem_trigPoly {D : ℕ} {F : ℝ → ℂ} (hF : F ∈ trigPoly D) {j : ℤ}
    (hj : (D : ℤ) < |j|) : coeff j F = 0 := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      rw [coeff_expMode, ite_eq_right_iff]
      rintro rfl
      exact absurd hk (not_le.mpr hj)
  | zero => exact coeff_zero_fun j
  | add x y hx' hy' hx hy =>
      rw [coeff_add (continuous_of_mem_trigPoly hx') (continuous_of_mem_trigPoly hy'), hx, hy,
        add_zero]
  | smul c x _ hx => rw [coeff_smul, hx, mul_zero]

/-- **Fourier inversion for trigonometric polynomials.** -/
theorem eq_sum_coeff_of_mem_trigPoly {D : ℕ} {F : ℝ → ℂ} (hF : F ∈ trigPoly D) (θ : ℝ) :
    F θ = (2 * (Real.pi : ℂ))⁻¹ *
      ∑ j ∈ Finset.Icc (-(D : ℤ)) D, coeff j F * expMode j θ := by
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  induction hF using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      have hkI : k ∈ Finset.Icc (-(D : ℤ)) D := Finset.mem_Icc.mpr (abs_le.mp hk)
      simp_rw [coeff_expMode, ite_mul, zero_mul]
      simp only [Finset.sum_ite_eq, hkI, ↓reduceIte]
      rw [← mul_assoc, inv_mul_cancel₀ hπ, one_mul]
  | zero =>
      simp [coeff_zero_fun]
  | add x y hx' hy' hx hy =>
      simp_rw [coeff_add (continuous_of_mem_trigPoly hx') (continuous_of_mem_trigPoly hy'), add_mul,
        Finset.sum_add_distrib, mul_add]
      rw [Pi.add_apply, hx, hy]
  | smul c x _ hx =>
      simp_rw [coeff_smul, mul_assoc, ← Finset.mul_sum]
      rw [Pi.smul_apply, smul_eq_mul, hx, mul_left_comm]

/-! ## Entries of rotated matrices -/

theorem rotMatrix_mul_apply {N p : ℕ} (h : p + 1 < N) (θ : ℝ) (A : Matrix (Fin N) (Fin N) ℝ)
    (i j : Fin N) :
    (rotMatrix h θ * A) i j =
      A i j + (Real.cos θ - 1) * (blockProj h * A) i j +
        Real.sin θ * (rotationGenerator N p * A) i j := by
  simp only [rotMatrix, Matrix.add_mul, Matrix.smul_mul, one_mul, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]

/-- The entries of `r_p(θ) A` are trigonometric polynomials of degree `1` in `θ`. -/
theorem entry_blockRotation_mul_mem_trigPoly {N p : ℕ} (h : p + 1 < N)
    (A : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    (fun θ : ℝ => ((((blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) * A) i j : ℝ) : ℂ)) ∈
      trigPoly 1 := by
  have e : (fun θ : ℝ => ((((blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) * A) i j : ℝ) : ℂ)) =
      fun θ : ℝ => ((A i j : ℝ) : ℂ) + ((Real.cos θ : ℂ) - 1) * (((blockProj h * A) i j : ℝ) : ℂ) +
        (Real.sin θ : ℂ) * (((rotationGenerator N p * A) i j : ℝ) : ℂ) := by
    funext θ
    rw [blockRotation_val_eq h, rotMatrix_mul_apply h]
    push_cast
    ring
  rw [e]
  exact affine_mem_trigPoly _ _ _

/-! ## `O(N)`-finite functions -/

variable {N p : ℕ}

/-- For a continuous right `O(N)`-finite function `f`, the functions `θ ↦ f(r_p(θ) g)` with
`g ∈ O(N)` are trigonometric polynomials of one common degree. -/
theorem exists_trigPoly_of_mem_kFiniteVectors (hp : p + 1 < N)
    {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : Continuous f)
    (hK : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
      (unitaryCompact ℝ N)) :
    ∃ D : ℕ, ∀ g ∈ unitaryCompact ℝ N, (fun θ => f (blockRotation N p θ * g)) ∈ trigPoly D := by
  obtain ⟨P, hP⟩ := OrthogonalFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors hf hK 1
  obtain ⟨D, hD⟩ := exists_eval_mem_trigPoly P
  refine ⟨D, fun g hg => ?_⟩
  have hmem : ∀ θ : ℝ, blockRotation N p θ * g ∈ unitaryCompact ℝ N := fun θ =>
    (unitaryCompact ℝ N).mul_mem (blockRotation_mem_unitaryCompact N p θ) hg
  have e : (fun θ => f (blockRotation N p θ * g)) = fun θ => MvPolynomial.eval
      (fun ij : Fin N × Fin N => (fun (ij : Fin N × Fin N) (θ : ℝ) =>
        ((((blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) * (g : Matrix (Fin N) (Fin N) ℝ))
          ij.1 ij.2 : ℝ) : ℂ)) ij θ) P := by
    funext θ
    have hθ := hP ⟨_, hmem θ⟩
    have hu : (1 : Langlands.GeneralLinear N ℝ) *
        Unitary.toUnits (⟨_, hmem θ⟩ : Matrix.unitaryGroup (Fin N) ℝ) =
          blockRotation N p θ * g := by
      rw [one_mul]
      exact Units.ext rfl
    rw [hu] at hθ
    rw [hθ]
    rfl
  rw [e]
  exact hD _ fun ij => entry_blockRotation_mul_mem_trigPoly hp _ ij.1 ij.2

/-- **Uniform finiteness of the Fourier modes on `O(N)`.** For a continuous right
`O(N)`-finite function `f` there is a bound `D` with `Φ_j f (g) = 0` for all `|j| > D` and all
`g ∈ O(N)`. -/
theorem exists_blockFourierCoefficient_eq_zero (hp : p + 1 < N)
    {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : Continuous f)
    (hK : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
      (unitaryCompact ℝ N)) :
    ∃ D : ℕ, ∀ j : ℤ, (D : ℤ) < |j| → ∀ g ∈ unitaryCompact ℝ N,
      blockFourierCoefficient N p j f g = 0 := by
  obtain ⟨D, hD⟩ := exists_trigPoly_of_mem_kFiniteVectors hp hf hK
  exact ⟨D, fun j hj g hg => coeff_eq_zero_of_mem_trigPoly (hD g hg) hj⟩

/-- **Fourier inversion on `O(N)`.** For a continuous right `O(N)`-finite function `f` there is a
bound `D` beyond which the Fourier modes vanish on `O(N)`, and
`f(r_p(θ) g) = (2π)⁻¹ Σ_{|j| ≤ D} Φ_j f (g) e^{ijθ}` for `g ∈ O(N)`. -/
theorem exists_eq_sum_blockFourierCoefficient (hp : p + 1 < N)
    {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : Continuous f)
    (hK : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
      (unitaryCompact ℝ N)) :
    ∃ D : ℕ, (∀ j : ℤ, (D : ℤ) < |j| → ∀ g ∈ unitaryCompact ℝ N,
      blockFourierCoefficient N p j f g = 0) ∧
      ∀ g ∈ unitaryCompact ℝ N, ∀ θ : ℝ, f (blockRotation N p θ * g) =
        (2 * (Real.pi : ℂ))⁻¹ *
          ∑ j ∈ Finset.Icc (-(D : ℤ)) D, blockFourierCoefficient N p j f g * expMode j θ := by
  obtain ⟨D, hD⟩ := exists_trigPoly_of_mem_kFiniteVectors hp hf hK
  exact ⟨D, fun j hj g hg => coeff_eq_zero_of_mem_trigPoly (hD g hg) hj,
    fun g hg θ => eq_sum_coeff_of_mem_trigPoly (hD g hg) θ⟩

/-- Only finitely many Fourier modes of a continuous right `O(N)`-finite function are nonzero at
a point of `O(N)`. -/
theorem finite_support_blockFourierCoefficient (hp : p + 1 < N)
    {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : Continuous f)
    (hK : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
      (unitaryCompact ℝ N)) {g : Langlands.GeneralLinear N ℝ} (hg : g ∈ unitaryCompact ℝ N) :
    (Function.support fun j : ℤ => blockFourierCoefficient N p j f g).Finite := by
  obtain ⟨D, hD⟩ := exists_blockFourierCoefficient_eq_zero hp hf hK
  refine (Finset.Icc (-(D : ℤ)) D).finite_toSet.subset fun j hj => ?_
  rw [Finset.coe_Icc, Set.mem_Icc, ← abs_le]
  by_contra hlt
  exact hj (hD j (not_le.mp hlt) g hg)

/-- **Reconstruction on `O(N)`.** `f(g) = (2π)⁻¹ Σᶠ_j Φ_j f (g)` for `g ∈ O(N)`. -/
theorem eq_finsum_blockFourierCoefficient (hp : p + 1 < N)
    {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : Continuous f)
    (hK : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
      (unitaryCompact ℝ N)) {g : Langlands.GeneralLinear N ℝ} (hg : g ∈ unitaryCompact ℝ N) :
    f g = (2 * (Real.pi : ℂ))⁻¹ * ∑ᶠ j : ℤ, blockFourierCoefficient N p j f g := by
  obtain ⟨D, hD, hsum⟩ := exists_eq_sum_blockFourierCoefficient hp hf hK
  have h0 := hsum g hg 0
  rw [blockRotation_zero, one_mul] at h0
  rw [h0, finsum_eq_sum_of_support_subset (s := Finset.Icc (-(D : ℤ)) D)]
  · simp [expMode]
  · intro j hj
    rw [Finset.coe_Icc, Set.mem_Icc, ← abs_le]
    by_contra hlt
    exact hj (hD j (not_le.mp hlt) g hg)

/-- **Fourier uniqueness on `O(N)`.** A continuous right `O(N)`-finite function all of whose
Fourier modes vanish at a point `g ∈ O(N)` vanishes at `g`. -/
theorem eq_zero_of_blockFourierCoefficient_eq_zero (hp : p + 1 < N)
    {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : Continuous f)
    (hK : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
      (unitaryCompact ℝ N)) {g : Langlands.GeneralLinear N ℝ} (hg : g ∈ unitaryCompact ℝ N)
    (h0 : ∀ j : ℤ, blockFourierCoefficient N p j f g = 0) : f g = 0 := by
  rw [eq_finsum_blockFourierCoefficient hp hf hK hg]
  simp [h0]

/-! ## Left rotation -/

theorem periodic_blockRotation_mul (hp : p + 1 < N) (f : Langlands.GeneralLinear N ℝ → ℂ)
    (g : Langlands.GeneralLinear N ℝ) :
    Function.Periodic (fun θ => f (blockRotation N p θ * g)) (2 * Real.pi) := fun θ => by
  simp only [blockRotation_add_two_pi hp]

/-- **Left rotation.** `Φ_j f (r_p(φ) g) = e^{ijφ} Φ_j f (g)`. -/
theorem blockFourierCoefficient_blockRotation_mul (hp : p + 1 < N)
    (f : Langlands.GeneralLinear N ℝ → ℂ) (j : ℤ) (φ : ℝ) (g : Langlands.GeneralLinear N ℝ) :
    blockFourierCoefficient N p j f (blockRotation N p φ * g) =
      Complex.exp ((j : ℂ) * (φ : ℂ) * Complex.I) * blockFourierCoefficient N p j f g := by
  rw [blockFourierCoefficient_eq_coeff, blockFourierCoefficient_eq_coeff]
  have e : (fun θ => f (blockRotation N p θ * (blockRotation N p φ * g))) =
      fun θ => (fun θ => f (blockRotation N p θ * g)) (θ + φ) := by
    funext θ
    simp only [← mul_assoc, ← blockRotation_add]
  rw [e, coeff_comp_add (periodic_blockRotation_mul hp f g)]
  rfl

/-! ## Principal series: signs -/

/-- The sign vector with `-1` at `i` and `1` elsewhere. -/
def signVec (i : Fin N) : Fin N → ℝˣ := fun k => if k = i then -1 else 1

theorem toUnits_signReflection (i : Fin N) :
    (Unitary.toUnits (signReflection N i) : Langlands.GeneralLinear N ℝ) =
      GeneralLinear.Iwasawa.diagonalUnits (signVec i) := by
  ext a b
  rw [Unitary.val_toUnits_apply, signReflection_val]
  change Matrix.diagonal _ a b = Matrix.diagonal (fun k => ((signVec i k : ℝˣ) : ℝ)) a b
  congr 2
  funext k
  unfold signVec
  split_ifs <;> simp

theorem principalSeriesCharacter_signVec {χ : ℕ → ℝˣ → ℂ} (hχ : ∀ i : ℕ, χ i 1 = 1)
    (i : Fin N) : principalSeriesCharacter ℝ N χ (signVec i) = χ i (-1) := by
  unfold principalSeriesCharacter
  have hval : ∀ k : Fin N, ‖((signVec i k : ℝˣ) : ℝ)‖ = 1 := fun k => by
    unfold signVec
    split_ifs <;> simp
  simp only [hval, one_pow, Complex.ofReal_one, Complex.one_cpow, mul_one]
  rw [Finset.prod_eq_single i (fun k _ hk => by simp [signVec, hk, hχ]) (by simp)]
  simp [signVec]

/-- A function of the principal series transforms under the sign matrix `s_i` by `χ_i(-1)`. -/
theorem apply_signReflection_mul {χ : ℕ → ℝˣ → ℂ} (hχ : ∀ i : ℕ, χ i 1 = 1)
    {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : f ∈ principalSeries ℝ N χ) (i : Fin N)
    (g : Langlands.GeneralLinear N ℝ) :
    f (Unitary.toUnits (signReflection N i) * g) = χ i (-1) * f g := by
  have h := hf.2 (signVec i) 1 g
  rw [OneMemClass.coe_one, mul_one, principalSeriesCharacter_signVec hχ] at h
  rw [toUnits_signReflection, h]

theorem toUnits_signReflection_mul_self (i : Fin N) :
    (Unitary.toUnits (signReflection N i) : Langlands.GeneralLinear N ℝ) *
        Unitary.toUnits (signReflection N i) = 1 := by
  rw [← map_mul, signReflection_mul_self, map_one]

theorem toUnits_signReflection_mul_mul_self (i : Fin N) (x : Langlands.GeneralLinear N ℝ) :
    (Unitary.toUnits (signReflection N i) : Langlands.GeneralLinear N ℝ) *
        (Unitary.toUnits (signReflection N i) * x) = x := by
  rw [← mul_assoc, toUnits_signReflection_mul_self, one_mul]

/-- **Parity.** For a principal series function, `(-1)^j Φ_j f (g) = χ_p(-1) χ_{p+1}(-1) Φ_j f (g)`. -/
theorem neg_one_zpow_mul_blockFourierCoefficient (hp : p + 1 < N) {χ : ℕ → ℝˣ → ℂ}
    (hχ : ∀ i : ℕ, χ i 1 = 1) {f : Langlands.GeneralLinear N ℝ → ℂ}
    (hf : f ∈ principalSeries ℝ N χ) (j : ℤ) (g : Langlands.GeneralLinear N ℝ) :
    (-1 : ℂ) ^ j * blockFourierCoefficient N p j f g =
      χ p (-1) * χ (p + 1) (-1) * blockFourierCoefficient N p j f g := by
  have h1 := blockFourierCoefficient_blockRotation_mul hp f j Real.pi g
  have hexp : Complex.exp ((j : ℂ) * (Real.pi : ℂ) * Complex.I) = (-1 : ℂ) ^ j := by
    rw [mul_assoc, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rw [hexp] at h1
  rw [← h1]
  unfold blockFourierCoefficient
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext θ
  have hc : blockRotation N p θ * (blockRotation N p Real.pi * g) =
      Unitary.toUnits (signReflection N (ia hp)) *
        (Unitary.toUnits (signReflection N (ib hp)) * (blockRotation N p θ * g)) := by
    rw [← mul_assoc, ← blockRotation_add, add_comm, blockRotation_add, blockRotation_pi hp]
    simp only [mul_assoc]
  rw [hc, apply_signReflection_mul hχ hf, apply_signReflection_mul hχ hf]
  simp only [ia, ib]
  ring

/-- **Parity.** For a principal series function, `Φ_j f` vanishes unless
`(-1)^j = χ_p(-1) χ_{p+1}(-1)`. -/
theorem blockFourierCoefficient_eq_zero_of_parity (hp : p + 1 < N) {χ : ℕ → ℝˣ → ℂ}
    (hχ : ∀ i : ℕ, χ i 1 = 1) {f : Langlands.GeneralLinear N ℝ → ℂ}
    (hf : f ∈ principalSeries ℝ N χ) {j : ℤ} (hj : (-1 : ℂ) ^ j ≠ χ p (-1) * χ (p + 1) (-1))
    (g : Langlands.GeneralLinear N ℝ) : blockFourierCoefficient N p j f g = 0 := by
  have h := neg_one_zpow_mul_blockFourierCoefficient hp hχ hf j g
  have h' : ((-1 : ℂ) ^ j - χ p (-1) * χ (p + 1) (-1)) * blockFourierCoefficient N p j f g = 0 := by
    rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hj)

/-- **Sign matrices in the block.** For `i ∈ {p, p + 1}` and a principal series function,
`Φ_j f (s_i g) = χ_i(-1) Φ_{-j} f (g)`. -/
theorem blockFourierCoefficient_signReflection_mul_of_mem (hp : p + 1 < N) {χ : ℕ → ℝˣ → ℂ}
    (hχ : ∀ i : ℕ, χ i 1 = 1) {f : Langlands.GeneralLinear N ℝ → ℂ}
    (hf : f ∈ principalSeries ℝ N χ) (i : Fin N) (hi : (i : ℕ) = p ∨ (i : ℕ) = p + 1) (j : ℤ)
    (g : Langlands.GeneralLinear N ℝ) :
    blockFourierCoefficient N p j f (Unitary.toUnits (signReflection N i) * g) =
      χ i (-1) * blockFourierCoefficient N p (-j) f g := by
  rw [blockFourierCoefficient_eq_coeff, blockFourierCoefficient_eq_coeff]
  have e : (fun θ => f (blockRotation N p θ * (Unitary.toUnits (signReflection N i) * g))) =
      χ i (-1) • fun θ => (fun θ => f (blockRotation N p θ * g)) (-θ) := by
    funext θ
    have hc : blockRotation N p θ * (Unitary.toUnits (signReflection N i) * g) =
        Unitary.toUnits (signReflection N i) * (blockRotation N p (-θ) * g) := by
      rw [← signReflection_mul_blockRotation_mul_of_mem hp i hi θ]
      simp only [mul_assoc, toUnits_signReflection_mul_mul_self]
    rw [Pi.smul_apply, smul_eq_mul, hc, apply_signReflection_mul hχ hf]
  rw [e, coeff_smul, coeff_comp_neg (periodic_blockRotation_mul hp f g)]

/-- **Sign matrices outside the block.** For `i ∉ {p, p + 1}` and a principal series function,
`Φ_j f (s_i g) = χ_i(-1) Φ_j f (g)`. -/
theorem blockFourierCoefficient_signReflection_mul_of_not_mem (hp : p + 1 < N)
    {χ : ℕ → ℝˣ → ℂ} (hχ : ∀ i : ℕ, χ i 1 = 1) {f : Langlands.GeneralLinear N ℝ → ℂ}
    (hf : f ∈ principalSeries ℝ N χ) (i : Fin N) (hi : (i : ℕ) ≠ p ∧ (i : ℕ) ≠ p + 1) (j : ℤ)
    (g : Langlands.GeneralLinear N ℝ) :
    blockFourierCoefficient N p j f (Unitary.toUnits (signReflection N i) * g) =
      χ i (-1) * blockFourierCoefficient N p j f g := by
  unfold blockFourierCoefficient
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext θ
  have hc : blockRotation N p θ * (Unitary.toUnits (signReflection N i) * g) =
      Unitary.toUnits (signReflection N i) * (blockRotation N p θ * g) := by
    conv_lhs => rw [← signReflection_mul_blockRotation_mul_of_not_mem hp i hi θ]
    simp only [mul_assoc, toUnits_signReflection_mul_mul_self]
  rw [hc, apply_signReflection_mul hχ hf, mul_assoc]

/-! ## Disjoint blocks -/

/-- **Disjoint blocks commute.** For blocks `p, p'` with `p + 1 < p'` or `p' + 1 < p` and a
continuous `f`, `Φ^p_j (Φ^{p'}_{j'} f) = Φ^{p'}_{j'} (Φ^p_j f)`. -/
theorem blockFourierCoefficient_comm {p' : ℕ} (hd : p + 1 < p' ∨ p' + 1 < p)
    {f : Langlands.GeneralLinear N ℝ → ℂ} (hf : Continuous f) (j j' : ℤ)
    (g : Langlands.GeneralLinear N ℝ) :
    blockFourierCoefficient N p j (blockFourierCoefficient N p' j' f) g =
      blockFourierCoefficient N p' j' (blockFourierCoefficient N p j f) g := by
  unfold blockFourierCoefficient
  simp_rw [← intervalIntegral.integral_mul_const]
  set F : ℝ → ℝ → ℂ := fun θ φ => f (blockRotation N p' φ * (blockRotation N p θ * g)) *
    Complex.exp (-((j' : ℂ) * (φ : ℂ) * Complex.I)) *
      Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) with hF
  have hcont : Continuous (Function.uncurry F) := by
    refine ((hf.comp ?_).mul ?_).mul ?_
    · exact (((continuous_blockRotation N p').comp continuous_snd).mul
        (((continuous_blockRotation N p).comp continuous_fst).mul continuous_const))
    · exact Complex.continuous_exp.comp (by fun_prop)
    · exact Complex.continuous_exp.comp (by fun_prop)
  have hint : MeasureTheory.IntegrableOn (Function.uncurry F)
      (Set.uIoc 0 (2 * Real.pi) ×ˢ Set.uIoc 0 (2 * Real.pi)) :=
    (hcont.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hswap := MeasureTheory.intervalIntegral_intervalIntegral_swap hint
  simp only [hF] at hswap
  rw [hswap]
  congr 1
  funext φ
  congr 1
  funext θ
  rw [← mul_assoc, ← mul_assoc, blockRotation_commute hd θ φ]
  ring

end RealBlockFourierFinite

end Langlands.Archimedean
