import Langlands.Global.Hecke.ArchGaussian
import Langlands.Global.Hecke.LatticePoissonGeneral
import Langlands.Global.Hecke.MixedSpaceUnfolding
import Langlands.Representation.GodementJacquet.WhittakerTorusCoordinates
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Fourier analysis on the mixed space

Let `V = mixedSpace K = ℝ^{r₁} × ℂ^{r₂}` with Lebesgue measure, and fix nonzero scalars
`aR v` (real places) and `aC v` (complex places). This module sets up the archimedean harmonic
analysis of the Tate–Hecke proof of the global functional equation:

* the additive trace `T(x) = ∑ aR v x_v + ∑ 2 Re (aC v x_v)` (`addTrace`), so that
  `x ↦ 𝐞 (T x)` is the product of the characters `x ↦ 𝐞 (a x)` and `z ↦ 𝐞 (2 Re (a z))`, and
  the symmetric nondegenerate pairing `B(x, y) = -T(x y)` (`tracePairing`), whose Mathlib
  Fourier transform is `∫ 𝐞 (T (x y)) f x dx`;
* the product Gaussian `mixedGaussian` and its Fourier transform
  (`fourierIntegral_mixedGaussian`), its Gaussian decay (`exists_norm_mixedGaussian_le`) and its
  zeta integral against a product character (`integral_mixedGaussian_mul_mixedCharFun`);
* the scaling rule for the Fourier transform (`fourierIntegral_comp_mul`);
* the covolume duality `vol(b) vol(b^*) κ² = 1` for a basis `b` and its dual basis
  (`measureReal_parallelepiped_mul_dualBasis`), where `κ = ∏ √|aR v| ∏ 2 |aC v|`.
-/

open MeasureTheory Set Filter Module Complex
open scoped Real ComplexConjugate FourierTransform Classical

noncomputable section

namespace Langlands.Global.Hecke

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace

/-! ### Elementary facts -/

lemma fourierChar_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((𝐞 (∑ i ∈ s, f i) : Circle) : ℂ) = ∏ i ∈ s, (𝐞 (f i) : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, Circle.coe_mul, ih]

lemma ofReal_sq_cpow {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    ((r ^ 2 : ℝ) : ℂ) ^ z = (r : ℂ) ^ (2 * z) := by
  rcases hr.eq_or_lt with h | h
  · subst h
    by_cases hz : z = 0
    · simp [hz]
    · simp [hz, zero_cpow]
  · have := ofReal_rpow_cpow h 2 z
    rw [Real.rpow_two] at this
    rw [this]
    push_cast
    rfl

lemma exists_pos_le_of_fintype {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ c, 0 < c ∧ ∀ i, c ≤ f i := by
  rcases isEmpty_or_nonempty ι with h | h
  · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
    exact ⟨f i₀, hf i₀, fun i => hi₀ i (Finset.mem_univ i)⟩

/-- `r ^ k e ^ {-b r²} ≤ C e ^ {-b r² / 2}` for `r ≥ 0`. -/
lemma exists_pow_mul_exp_neg_le (k : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ C, 0 < C ∧ ∀ r : ℝ, 0 ≤ r →
      r ^ k * Real.exp (-(b * r ^ 2)) ≤ C * Real.exp (-(b / 2 * r ^ 2)) := by
  refine ⟨1 + k.factorial * (2 / b) ^ k, by positivity, fun r hr => ?_⟩
  have hsplit : Real.exp (-(b * r ^ 2)) =
      Real.exp (-(b / 2 * r ^ 2)) * Real.exp (-(b / 2 * r ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  -- `r ^ k ≤ (1 + k! (2/b)^k) e ^ {b r² / 2}`
  have hE : 1 ≤ Real.exp (b / 2 * r ^ 2) := Real.one_le_exp (by positivity)
  have hfac := Real.pow_div_factorial_le_exp (x := b / 2 * r ^ 2) (by positivity) k
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have h2 : r ^ (2 * k) ≤ k.factorial * (2 / b) ^ k * Real.exp (b / 2 * r ^ 2) := by
    rw [div_le_iff₀ hk, mul_pow] at hfac
    have : r ^ (2 * k) = (2 / b) ^ k * ((b / 2) ^ k * (r ^ 2) ^ k) := by
      rw [← mul_assoc, ← mul_pow, div_mul_div_comm, mul_comm 2 b, div_self (by positivity),
        one_pow, one_mul, ← pow_mul]
    rw [this]
    calc (2 / b) ^ k * ((b / 2) ^ k * (r ^ 2) ^ k)
        ≤ (2 / b) ^ k * (Real.exp (b / 2 * r ^ 2) * k.factorial) :=
          mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = _ := by ring
  have hrk : r ^ k ≤ 1 + r ^ (2 * k) := by
    rcases le_total r 1 with h1 | h1
    · have := pow_le_one₀ hr h1 (n := k)
      linarith [pow_nonneg hr (2 * k)]
    · have := pow_le_pow_right₀ h1 (show k ≤ 2 * k by omega)
      linarith
  have hexp_inv : Real.exp (-(b / 2 * r ^ 2)) * Real.exp (b / 2 * r ^ 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc r ^ k * Real.exp (-(b / 2 * r ^ 2))
      ≤ (1 + r ^ (2 * k)) * Real.exp (-(b / 2 * r ^ 2)) :=
        mul_le_mul_of_nonneg_right hrk (Real.exp_pos _).le
    _ ≤ (Real.exp (b / 2 * r ^ 2) + k.factorial * (2 / b) ^ k * Real.exp (b / 2 * r ^ 2)) *
          Real.exp (-(b / 2 * r ^ 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        linarith
    _ = 1 + k.factorial * (2 / b) ^ k := by
        have : (Real.exp (b / 2 * r ^ 2) + k.factorial * (2 / b) ^ k * Real.exp (b / 2 * r ^ 2)) *
            Real.exp (-(b / 2 * r ^ 2)) =
            (1 + k.factorial * (2 / b) ^ k) *
              (Real.exp (-(b / 2 * r ^ 2)) * Real.exp (b / 2 * r ^ 2)) := by ring
        rw [this, hexp_inv, mul_one]

/-- Gaussian decay implies polynomial decay of any order: `e ^ {-c u²} ≤ C (1 + u) ^ {-r}`. -/
lemma exists_exp_neg_mul_sq_le_rpow {c : ℝ} (hc : 0 < c) (r : ℝ) :
    ∃ C, 0 < C ∧ ∀ u : ℝ, 0 ≤ u → Real.exp (-(c * u ^ 2)) ≤ C * (1 + u) ^ (-r) := by
  obtain ⟨k, hk⟩ := exists_nat_ge r
  obtain ⟨C, hC, hCb⟩ := exists_pow_mul_exp_neg_le k (show 0 < c / 2 by positivity)
  refine ⟨Real.exp c * C, by positivity, fun u hu => ?_⟩
  have hv : 1 ≤ 1 + u := by linarith
  have hv0 : 0 < 1 + u := by linarith
  -- `u² ≥ (1 + u)² / 2 - 1`
  have hsq : -(c * u ^ 2) ≤ c + -(c / 2 * (1 + u) ^ 2) := by nlinarith [sq_nonneg (u - 1)]
  have h1 : Real.exp (-(c * u ^ 2)) ≤ Real.exp c * Real.exp (-(c / 2 * (1 + u) ^ 2)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr hsq
  have h2 := hCb (1 + u) hv0.le
  have h3 : Real.exp (-(c / 2 * (1 + u) ^ 2)) ≤ C * ((1 + u) ^ k)⁻¹ := by
    have hpos : 0 < (1 + u) ^ k := by positivity
    rw [le_mul_inv_iff₀ hpos]
    calc Real.exp (-(c / 2 * (1 + u) ^ 2)) * (1 + u) ^ k
        = (1 + u) ^ k * Real.exp (-(c / 2 * (1 + u) ^ 2)) := mul_comm _ _
      _ ≤ C * Real.exp (-(c / 2 / 2 * (1 + u) ^ 2)) := h2
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (by have := sq_nonneg (1 + u); nlinarith)) hC.le
      _ = C := mul_one C
  have h4 : ((1 + u) ^ k)⁻¹ ≤ (1 + u) ^ (-r) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hv0.le]
    exact Real.rpow_le_rpow_of_exponent_le hv (by linarith)
  calc Real.exp (-(c * u ^ 2)) ≤ Real.exp c * Real.exp (-(c / 2 * (1 + u) ^ 2)) := h1
    _ ≤ Real.exp c * (C * ((1 + u) ^ k)⁻¹) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ Real.exp c * (C * (1 + u) ^ (-r)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hC.le) (by positivity)
    _ = Real.exp c * C * (1 + u) ^ (-r) := by ring

/-! ### One-dimensional Gaussians -/

theorem norm_realGaussian (b : ℝ) (p : ℕ) (x : ℝ) :
    ‖realGaussian b p x‖ = |x| ^ p * Real.exp (-(π * b * x ^ 2)) := by
  have : (-(π * b * (x : ℂ) ^ 2) : ℂ) = ((-(π * b * x ^ 2) : ℝ) : ℂ) := by push_cast; ring
  rw [realGaussian, norm_mul, norm_pow, this, Complex.norm_exp_ofReal, Complex.norm_real,
    Real.norm_eq_abs]

theorem norm_complexGaussian (b : ℝ) (N : ℤ) (z : ℂ) :
    ‖complexGaussian b N z‖ = ‖z‖ ^ N.natAbs * Real.exp (-(2 * π * b * ‖z‖ ^ 2)) := by
  have : (-(2 * π * b * ((‖z‖ : ℝ) : ℂ) ^ 2) : ℂ) = ((-(2 * π * b * ‖z‖ ^ 2) : ℝ) : ℂ) := by
    push_cast; ring
  rw [complexGaussian, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, this,
    Complex.norm_exp_ofReal, ← pow_add, Int.toNat_add_toNat_neg_eq_natAbs]

theorem continuous_realGaussian (b : ℝ) (p : ℕ) : Continuous (realGaussian b p) := by
  unfold realGaussian; fun_prop

theorem continuous_complexGaussian (b : ℝ) (N : ℤ) : Continuous (complexGaussian b N) := by
  unfold complexGaussian; fun_prop

/-- The Fourier transform of the real adapted Gaussian of parity `p`. -/
theorem integral_realGaussian_mul_fourierChar {a : ℝ} (ha : a ≠ 0) (p : Fin 2) (y : ℝ) :
    ∫ x : ℝ, realGaussian |a| p x * 𝐞 (a * x * y) =
      ((Real.sqrt |a|)⁻¹ : ℝ) * (I * ((a / |a| : ℝ) : ℂ)) ^ (p : ℕ) * realGaussian |a| p y := by
  obtain ⟨k, hk⟩ := p
  interval_cases k
  · simpa using integral_realGaussian_zero_mul_fourierChar ha y
  · simpa using integral_realGaussian_one_mul_fourierChar ha y

variable {K : Type*} [Field K] [NumberField K]

local notation "V" => mixedSpace K

/-! ### The norm on the mixed space -/

lemma norm_eq_prod_real_complex (x : V) :
    mixedEmbedding.norm x = (∏ v, |x.1 v|) * ∏ v, ‖x.2 v‖ ^ 2 := by
  rw [mixedEmbedding.norm_apply, prod_eq_prod_mul_prod]
  congr 1 <;> refine Finset.prod_congr rfl fun v _ => ?_
  · rw [normAtPlace_apply_of_isReal v.2, mult_isReal, pow_one, Real.norm_eq_abs]
  · rw [normAtPlace_apply_of_isComplex v.2, mult_isComplex]

lemma sq_norm_le_sum (x : V) : ‖x‖ ^ 2 ≤ ∑ v, x.1 v ^ 2 + ∑ v, ‖x.2 v‖ ^ 2 := by
  have h1 : ‖x.1‖ ≤ Real.sqrt (∑ v, x.1 v ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun v => ?_
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun v => x.1 v ^ 2)
      (fun v _ => sq_nonneg _) (Finset.mem_univ v))
  have h2 : ‖x.2‖ ≤ Real.sqrt (∑ v, ‖x.2 v‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun v => ?_
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun v => ‖x.2 v‖ ^ 2) (fun v _ => sq_nonneg _)
      (Finset.mem_univ v)
  have hS1 : 0 ≤ ∑ v, x.1 v ^ 2 := Finset.sum_nonneg fun v _ => sq_nonneg _
  have hS2 : 0 ≤ ∑ v, ‖x.2 v‖ ^ 2 := Finset.sum_nonneg fun v _ => sq_nonneg _
  have e1 : ‖x.1‖ ^ 2 ≤ ∑ v, x.1 v ^ 2 := by
    calc ‖x.1‖ ^ 2 ≤ Real.sqrt (∑ v, x.1 v ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = _ := Real.sq_sqrt hS1
  have e2 : ‖x.2‖ ^ 2 ≤ ∑ v, ‖x.2 v‖ ^ 2 := by
    calc ‖x.2‖ ^ 2 ≤ Real.sqrt (∑ v, ‖x.2 v‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ = _ := Real.sq_sqrt hS2
  rw [Prod.norm_def]
  rcases le_total ‖x.1‖ ‖x.2‖ with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

/-! ### The additive trace and the trace pairing -/

section Pairing

variable (aR : {w : InfinitePlace K // IsReal w} → ℝ)
  (aC : {w : InfinitePlace K // IsComplex w} → ℂ)

/-- The additive trace `T(x) = ∑ aR v x_v + ∑ 2 Re (aC v x_v)` on the mixed space. -/
def addTrace : V →ₗ[ℝ] ℝ where
  toFun x := ∑ v, aR v * x.1 v + ∑ v, 2 * (aC v * x.2 v).re
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, add_re,
      Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Complex.real_smul, mul_add, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun v _ => ?_
    · ring
    · rw [mul_left_comm, re_ofReal_mul]; ring

lemma addTrace_apply (x : V) :
    addTrace aR aC x = ∑ v, aR v * x.1 v + ∑ v, 2 * (aC v * x.2 v).re := rfl

/-- The character `x ↦ 𝐞 (T x)` is the product of the local characters. -/
lemma fourierChar_addTrace (x : V) :
    (𝐞 (addTrace aR aC x) : ℂ) =
      (∏ v, (𝐞 (aR v * x.1 v) : ℂ)) * ∏ v, (𝐞 (2 * (aC v * x.2 v).re) : ℂ) := by
  rw [addTrace_apply, AddChar.map_add_eq_mul, Circle.coe_mul, fourierChar_sum, fourierChar_sum]

/-- The pairing `B(x, y) = -T(x y)`. With this sign, Mathlib's Fourier transform
`∫ 𝐞 (-B x y) f x dx` is `∫ 𝐞 (T (x y)) f x dx`. -/
def tracePairing : LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun x y => -addTrace aR aC (x * y))
    (fun x x' y => by simp only [add_mul, map_add, neg_add])
    (fun c x y => by simp only [smul_mul_assoc, map_smul, smul_eq_mul, mul_neg])
    (fun x y y' => by simp only [mul_add, map_add, neg_add])
    (fun c x y => by simp only [mul_smul_comm, map_smul, smul_eq_mul, mul_neg])

@[simp] lemma tracePairing_apply (x y : V) :
    tracePairing aR aC x y = -addTrace aR aC (x * y) := rfl

lemma tracePairing_comm (x y : V) : tracePairing aR aC x y = tracePairing aR aC y x := by
  simp only [tracePairing_apply, mul_comm]

lemma tracePairing_isSymm : (tracePairing aR aC).IsSymm :=
  LinearMap.BilinForm.isSymm_def.mpr (tracePairing_comm aR aC)

lemma tracePairing_flip_isSymm : (tracePairing aR aC).flip.IsSymm :=
  LinearMap.BilinForm.isSymm_def.mpr fun x y => tracePairing_comm aR aC y x

lemma addTrace_mul_conj (x : V) :
    addTrace aR aC (x * (fun v => aR v * x.1 v, fun v => conj (aC v * x.2 v))) =
      ∑ v, (aR v * x.1 v) ^ 2 + ∑ v, 2 * ‖aC v * x.2 v‖ ^ 2 := by
  simp only [addTrace_apply, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply]
  congr 1 <;> refine Finset.sum_congr rfl fun v _ => ?_
  · ring
  · rw [← mul_assoc, mul_conj, ofReal_re, Complex.normSq_eq_norm_sq]

variable {aR aC}

lemma tracePairing_nondegenerate (haR : ∀ v, aR v ≠ 0) (haC : ∀ v, aC v ≠ 0) :
    (tracePairing aR aC).Nondegenerate := by
  refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun x hx => ?_
  have h := hx (fun v => aR v * x.1 v, fun v => conj (aC v * x.2 v))
  rw [tracePairing_apply, neg_eq_zero, addTrace_mul_conj] at h
  have h1 : 0 ≤ ∑ v, (aR v * x.1 v) ^ 2 := Finset.sum_nonneg fun v _ => sq_nonneg _
  have h2 : 0 ≤ ∑ v, 2 * ‖aC v * x.2 v‖ ^ 2 := Finset.sum_nonneg fun v _ => by positivity
  have e1 := (Finset.sum_eq_zero_iff_of_nonneg fun v _ => sq_nonneg (aR v * x.1 v)).mp
    (by linarith)
  have e2 := (Finset.sum_eq_zero_iff_of_nonneg
    fun v _ => (by positivity : (0 : ℝ) ≤ 2 * ‖aC v * x.2 v‖ ^ 2)).mp (by linarith)
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · have := e1 v (Finset.mem_univ v)
    simpa [haR v] using this
  · have := e2 v (Finset.mem_univ v)
    simpa [haC v] using this

variable (aR aC)

/-- Mathlib's Fourier transform for the trace pairing is Tate's: `∫ 𝐞 (T (x w)) f x dx`. -/
lemma fourierIntegral_tracePairing_eq (f : V → ℂ) (w : V) :
    VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) f w =
      ∫ x, (𝐞 (addTrace aR aC (x * w)) : ℂ) * f x := by
  simp only [VectorFourier.fourierIntegral, tracePairing_apply, neg_neg, Circle.smul_def,
    smul_eq_mul]

/-- **Scaling.** For `y` with `N(y) ≠ 0`, the Fourier transform of `x ↦ f (y x)` at `w` is
`N(y)⁻¹` times the Fourier transform of `f` at `y⁻¹ w`. -/
theorem fourierIntegral_comp_mul (f : V → ℂ) {y : V} (hy : mixedEmbedding.norm y ≠ 0) (w : V) :
    VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) (fun x => f (y * x)) w =
      ((mixedEmbedding.norm y)⁻¹ : ℝ) *
        VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) f (y⁻¹ * w) := by
  rw [fourierIntegral_tracePairing_eq, fourierIntegral_tracePairing_eq]
  have hyy := mul_inv_cancel_of_norm_ne_zero hy
  have h := integral_comp_mul_left hy
    (fun u => (𝐞 (addTrace aR aC (u * (y⁻¹ * w))) : ℂ) * f u)
  have hxw : ∀ x : V, y * x * (y⁻¹ * w) = x * w := fun x => by
    calc y * x * (y⁻¹ * w) = (y * y⁻¹) * (x * w) := by ring
      _ = x * w := by rw [hyy, one_mul]
  simp only [hxw] at h
  rw [h, Complex.real_smul]

end Pairing

/-! ### The product Gaussian -/

section Gaussian

variable (aR : {w : InfinitePlace K // IsReal w} → ℝ)
  (aC : {w : InfinitePlace K // IsComplex w} → ℂ)
  (p : {w : InfinitePlace K // IsReal w} → Fin 2) (N : {w : InfinitePlace K // IsComplex w} → ℤ)

/-- The product of the adapted Gaussians `x ^ p e ^ {-π |a| x²}` (real places) and
`z̄ ^ N e ^ {-2π |a| |z|²}` (complex places; `z ^ {-N}` if `N < 0`). -/
def mixedGaussian (x : V) : ℂ :=
  (∏ v, realGaussian |aR v| (p v) (x.1 v)) * ∏ v, complexGaussian ‖aC v‖ (N v) (x.2 v)

/-- The constant in the Fourier transform of `mixedGaussian`. -/
def mixedGaussianFTConst : ℂ :=
  (∏ v, ((Real.sqrt |aR v|)⁻¹ : ℝ) * (I * ((aR v / |aR v| : ℝ) : ℂ)) ^ (p v : ℕ)) *
    ∏ v, ((2 * ‖aC v‖)⁻¹ : ℝ) * (I ^ (N v).natAbs * (aC v / ‖aC v‖) ^ (N v))

theorem continuous_mixedGaussian : Continuous (mixedGaussian aR aC p N) := by
  unfold mixedGaussian
  refine Continuous.mul (continuous_finsetProd _ fun v _ => ?_)
    (continuous_finsetProd _ fun v _ => ?_)
  · exact (continuous_realGaussian _ _).comp ((continuous_apply v).comp continuous_fst)
  · exact (continuous_complexGaussian _ _).comp ((continuous_apply v).comp continuous_snd)

variable {aR aC}

/-- **Fourier transform of the product Gaussian**:
`∫ 𝐞 (T (x w)) F_{p,N} (x) dx = c_{p,N} F_{p,-N} (w)`. -/
theorem fourierIntegral_mixedGaussian (haR : ∀ v, aR v ≠ 0) (haC : ∀ v, aC v ≠ 0) (w : V) :
    VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) (mixedGaussian aR aC p N) w =
      mixedGaussianFTConst aR aC p N * mixedGaussian aR aC p (-N) w := by
  rw [fourierIntegral_tracePairing_eq]
  have hint : ∀ x : V, (𝐞 (addTrace aR aC (x * w)) : ℂ) * mixedGaussian aR aC p N x =
      (∏ v, realGaussian |aR v| (p v) (x.1 v) * 𝐞 (aR v * x.1 v * w.1 v)) *
        ∏ v, complexGaussian ‖aC v‖ (N v) (x.2 v) * 𝐞 (2 * (aC v * x.2 v * w.2 v).re) := by
    intro x
    rw [fourierChar_addTrace, mixedGaussian, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, mul_assoc]
    ring
  simp_rw [hint]
  rw [Measure.volume_eq_prod, integral_prod_mul
    (fun x₁ : {w : InfinitePlace K // IsReal w} → ℝ =>
      ∏ v, realGaussian |aR v| (p v) (x₁ v) * 𝐞 (aR v * x₁ v * w.1 v))
    (fun x₂ : {w : InfinitePlace K // IsComplex w} → ℂ =>
      ∏ v, complexGaussian ‖aC v‖ (N v) (x₂ v) * 𝐞 (2 * (aC v * x₂ v * w.2 v).re)),
    integral_fintype_prod_volume_eq_prod
      (fun v (t : ℝ) => realGaussian |aR v| (p v) t * 𝐞 (aR v * t * w.1 v)),
    integral_fintype_prod_volume_eq_prod
      (fun v (z : ℂ) => complexGaussian ‖aC v‖ (N v) z * 𝐞 (2 * (aC v * z * w.2 v).re))]
  simp only [integral_realGaussian_mul_fourierChar (haR _),
    integral_complexGaussian_mul_fourierChar (haC _)]
  rw [mixedGaussianFTConst, mixedGaussian]
  simp only [Pi.neg_apply, Finset.prod_mul_distrib]
  ring

/-- **Gaussian decay**: `‖F_{p,N} (x)‖ ≤ C e ^ {-c ‖x‖²}` for some `C` and `c > 0`. -/
theorem exists_norm_mixedGaussian_le (haR : ∀ v, aR v ≠ 0) (haC : ∀ v, aC v ≠ 0) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ x : V, ‖mixedGaussian aR aC p N x‖ ≤ C * Real.exp (-(c * ‖x‖ ^ 2)) := by
  have hR : ∀ v, ∃ C, 0 < C ∧ ∀ r : ℝ, 0 ≤ r →
      r ^ (p v : ℕ) * Real.exp (-(π * |aR v| * r ^ 2)) ≤
        C * Real.exp (-(π * |aR v| / 2 * r ^ 2)) :=
    fun v => exists_pow_mul_exp_neg_le _ (by have := abs_pos.mpr (haR v); positivity)
  have hC : ∀ v, ∃ C, 0 < C ∧ ∀ r : ℝ, 0 ≤ r →
      r ^ (N v).natAbs * Real.exp (-(2 * π * ‖aC v‖ * r ^ 2)) ≤
        C * Real.exp (-(2 * π * ‖aC v‖ / 2 * r ^ 2)) :=
    fun v => exists_pow_mul_exp_neg_le _ (by have := norm_pos_iff.mpr (haC v); positivity)
  choose CR hCR hCRb using hR
  choose CC hCC hCCb using hC
  obtain ⟨c₁, hc₁, hc₁le⟩ := exists_pos_le_of_fintype (fun v => π * |aR v| / 2)
    fun v => by have := abs_pos.mpr (haR v); positivity
  obtain ⟨c₂, hc₂, hc₂le⟩ := exists_pos_le_of_fintype (fun v => 2 * π * ‖aC v‖ / 2)
    fun v => by have := norm_pos_iff.mpr (haC v); positivity
  refine ⟨(∏ v, CR v) * ∏ v, CC v, min c₁ c₂,
    mul_pos (Finset.prod_pos fun v _ => hCR v) (Finset.prod_pos fun v _ => hCC v),
    lt_min hc₁ hc₂, fun x => ?_⟩
  set c := min c₁ c₂
  have hbR : ∀ v, ‖realGaussian |aR v| (p v) (x.1 v)‖ ≤ CR v * Real.exp (-(c * x.1 v ^ 2)) := by
    intro v
    rw [norm_realGaussian]
    refine (hCRb v |x.1 v| (abs_nonneg _) |>.trans_eq' ?_).trans ?_
    · rw [sq_abs]
    · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hCR v).le
      rw [sq_abs]
      have := (min_le_left c₁ c₂).trans (hc₁le v)
      nlinarith [sq_nonneg (x.1 v)]
  have hbC : ∀ v, ‖complexGaussian ‖aC v‖ (N v) (x.2 v)‖ ≤
      CC v * Real.exp (-(c * ‖x.2 v‖ ^ 2)) := by
    intro v
    rw [norm_complexGaussian]
    refine (hCCb v ‖x.2 v‖ (norm_nonneg _)).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hCC v).le
    have := (min_le_right c₁ c₂).trans (hc₂le v)
    nlinarith [sq_nonneg ‖x.2 v‖]
  have hprod : ‖mixedGaussian aR aC p N x‖ ≤
      ((∏ v, CR v) * ∏ v, CC v) *
        Real.exp (-(c * (∑ v, x.1 v ^ 2 + ∑ v, ‖x.2 v‖ ^ 2))) := by
    rw [mixedGaussian, norm_mul, norm_prod, norm_prod]
    have e : Real.exp (-(c * (∑ v, x.1 v ^ 2 + ∑ v, ‖x.2 v‖ ^ 2))) =
        (∏ v, Real.exp (-(c * x.1 v ^ 2))) * ∏ v, Real.exp (-(c * ‖x.2 v‖ ^ 2)) := by
      rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add, mul_add, neg_add, Finset.mul_sum,
        Finset.mul_sum, Finset.sum_neg_distrib, Finset.sum_neg_distrib]
    rw [e]
    calc (∏ v, ‖realGaussian |aR v| (p v) (x.1 v)‖) * ∏ v, ‖complexGaussian ‖aC v‖ (N v) (x.2 v)‖
        ≤ (∏ v, CR v * Real.exp (-(c * x.1 v ^ 2))) *
            ∏ v, CC v * Real.exp (-(c * ‖x.2 v‖ ^ 2)) :=
          mul_le_mul (Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ => hbR v)
            (Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ => hbC v)
            (Finset.prod_nonneg fun v _ => norm_nonneg _)
            (Finset.prod_nonneg fun v _ => mul_nonneg (hCR v).le (Real.exp_pos _).le)
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]; ring
  refine hprod.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
    (mul_pos (Finset.prod_pos fun v _ => hCR v) (Finset.prod_pos fun v _ => hCC v)).le)
  have := sq_norm_le_sum x
  have hc : 0 < c := lt_min hc₁ hc₂
  nlinarith

/-- **Polynomial decay** of any order. -/
theorem exists_norm_mixedGaussian_le_rpow (haR : ∀ v, aR v ≠ 0) (haC : ∀ v, aC v ≠ 0)
    (r : ℝ) : ∃ C, ∀ x : V, ‖mixedGaussian aR aC p N x‖ ≤ C * (1 + ‖x‖) ^ (-r) := by
  obtain ⟨C, c, hC, hc, hb⟩ := exists_norm_mixedGaussian_le p N haR haC
  obtain ⟨D, hD, hDb⟩ := exists_exp_neg_mul_sq_le_rpow hc r
  refine ⟨C * D, fun x => (hb x).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hDb ‖x‖ (norm_nonneg x)) hC.le

end Gaussian

/-! ### The zeta integral of the product Gaussian -/

section Zeta

variable (aR : {w : InfinitePlace K // IsReal w} → ℝ)
  (aC : {w : InfinitePlace K // IsComplex w} → ℂ)
  (p : {w : InfinitePlace K // IsReal w} → Fin 2) (t : {w : InfinitePlace K // IsReal w} → ℂ)
  (N : {w : InfinitePlace K // IsComplex w} → ℤ) (u : {w : InfinitePlace K // IsComplex w} → ℂ)

/-- The product character `x ↦ ∏ (x_v / |x_v|) ^ p_v |x_v| ^ t_v ∏ (z_v / |z_v|) ^ N_v |z_v| ^ (2 u_v)`
on the mixed space. -/
def mixedCharFun (x : V) : ℂ :=
  (∏ v, realCharFun (p v) (t v) (x.1 v)) * ∏ v, complexCharFun (N v) (u v) (x.2 v)

lemma ofReal_inv_cpow_of_nonneg {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    ((r⁻¹ : ℝ) : ℂ) ^ z = (r : ℂ) ^ (-z) := by
  rw [ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hr]; exact Real.pi_pos.ne), cpow_neg]

/-- Inverting the argument of the real character inverts its unramified exponent. -/
theorem realCharFun_inv (p : ℕ) (t : ℂ) (x : ℝ) : realCharFun p t x⁻¹ = realCharFun p (-t) x := by
  have hs : x⁻¹ / |x⁻¹| = x / |x| := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [abs_inv, div_inv_eq_mul, inv_mul_eq_div, div_eq_div_iff hx (abs_ne_zero.mpr hx),
        abs_mul_abs_self]
  rw [realCharFun, realCharFun, hs, abs_inv, ofReal_inv_cpow_of_nonneg (abs_nonneg x)]

/-- Inverting the argument of the complex character inverts it. -/
theorem complexCharFun_inv (N : ℤ) (u : ℂ) (z : ℂ) :
    complexCharFun N u z⁻¹ = complexCharFun (-N) (-u) z := by
  rw [complexCharFun, complexCharFun, norm_inv, ofReal_inv_cpow_of_nonneg (norm_nonneg z),
    ofReal_inv, div_inv_eq_mul, inv_mul_eq_div, ← inv_div, inv_zpow', mul_neg]

/-- Inverting the argument of the product character inverts it. -/
theorem mixedCharFun_inv (x : V) :
    mixedCharFun p t N u x⁻¹ = mixedCharFun p (-t) (-N) (-u) x := by
  simp only [mixedCharFun, Prod.fst_inv, Prod.snd_inv, Pi.inv_apply, realCharFun_inv,
    complexCharFun_inv, Pi.neg_apply]

variable {aR aC}

/-- **Zeta integral of the product Gaussian**: for `Re (s + t_v + p_v) > 0` and
`Re (s + u_v + |N_v|/2) > 0`,
`∫ F_{p,N} χ N(x) ^ (s - 1) dx = ∏ |a_v| ^ {-(s + t_v + p_v)/2} Γ_ℝ(s + t_v + p_v)
 ∏ (π/2) |a_v| ^ {-(s + u_v + |N_v|/2)} Γ_ℂ(s + u_v + |N_v|/2)`. -/
theorem integral_mixedGaussian_mul_mixedCharFun (haR : ∀ v, aR v ≠ 0) (haC : ∀ v, aC v ≠ 0)
    (s : ℂ) (hR : ∀ v, 0 < (s + t v + (p v : ℕ)).re)
    (hC : ∀ v, 0 < (s + u v + (N v).natAbs / 2).re) :
    ∫ x : V, mixedGaussian aR aC p N x * mixedCharFun p t N u x *
        ((mixedEmbedding.norm x : ℝ) : ℂ) ^ (s - 1) =
      (∏ v, ((|aR v| : ℝ) : ℂ) ^ (-(s + t v + (p v : ℕ)) / 2) * Gammaℝ (s + t v + (p v : ℕ))) *
        ∏ v, (π / 2 : ℂ) * ((‖aC v‖ : ℝ) : ℂ) ^ (-(s + u v + (N v).natAbs / 2)) *
          Gammaℂ (s + u v + (N v).natAbs / 2) := by
  have hint : ∀ x : V, mixedGaussian aR aC p N x * mixedCharFun p t N u x *
      ((mixedEmbedding.norm x : ℝ) : ℂ) ^ (s - 1) =
      (∏ v, realGaussian |aR v| (p v) (x.1 v) * realCharFun (p v) (t v) (x.1 v) *
        ((|x.1 v| : ℝ) : ℂ) ^ (s - 1)) *
      ∏ v, complexGaussian ‖aC v‖ (N v) (x.2 v) * complexCharFun (N v) (u v) (x.2 v) *
        ((‖x.2 v‖ : ℝ) : ℂ) ^ (2 * (s - 1)) := by
    intro x
    rw [norm_eq_prod_real_complex, ofReal_mul,
      mul_cpow_ofReal_nonneg (Finset.prod_nonneg fun v _ => abs_nonneg _)
        (Finset.prod_nonneg fun v _ => sq_nonneg _),
      Langlands.GodementJacquet.WhittakerTorus.ofReal_prod_cpow _ _ (fun v _ => abs_nonneg _),
      Langlands.GodementJacquet.WhittakerTorus.ofReal_prod_cpow _ _ (fun v _ => sq_nonneg _)]
    simp only [ofReal_sq_cpow (norm_nonneg _)]
    rw [mixedGaussian, mixedCharFun, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  simp_rw [hint]
  rw [Measure.volume_eq_prod, integral_prod_mul
    (fun x₁ : {w : InfinitePlace K // IsReal w} → ℝ =>
      ∏ v, realGaussian |aR v| (p v) (x₁ v) * realCharFun (p v) (t v) (x₁ v) *
        ((|x₁ v| : ℝ) : ℂ) ^ (s - 1))
    (fun x₂ : {w : InfinitePlace K // IsComplex w} → ℂ =>
      ∏ v, complexGaussian ‖aC v‖ (N v) (x₂ v) * complexCharFun (N v) (u v) (x₂ v) *
        ((‖x₂ v‖ : ℝ) : ℂ) ^ (2 * (s - 1))),
    integral_fintype_prod_volume_eq_prod
      (fun v (x : ℝ) => realGaussian |aR v| (p v) x * realCharFun (p v) (t v) x *
        ((|x| : ℝ) : ℂ) ^ (s - 1)),
    integral_fintype_prod_volume_eq_prod
      (fun v (z : ℂ) => complexGaussian ‖aC v‖ (N v) z * complexCharFun (N v) (u v) z *
        ((‖z‖ : ℝ) : ℂ) ^ (2 * (s - 1)))]
  congr 1
  · refine Finset.prod_congr rfl fun v _ => ?_
    exact integral_realGaussian_mul_realCharFun (abs_pos.mpr (haR v)) _ _ _ (hR v)
  · refine Finset.prod_congr rfl fun v _ => ?_
    exact integral_complexGaussian_mul_complexCharFun (norm_pos_iff.mpr (haC v)) _ _ _ (hC v)

end Zeta

/-! ### Covolume duality -/

section Covolume

variable (aR : {w : InfinitePlace K // IsReal w} → ℝ)
  (aC : {w : InfinitePlace K // IsComplex w} → ℂ)

/-- The constant `κ = ∏ √|aR v| ∏ 2 |aC v|`: the Fourier transform of the plain Gaussian
`mixedGaussian aR aC 0 0` is `κ⁻¹` times itself. -/
def mixedGaussianConst : ℝ :=
  (∏ v, Real.sqrt |aR v|) * ∏ v, 2 * ‖aC v‖

/-- The plain Gaussian `mixedGaussian aR aC 0 0` as a real-valued function. -/
def mixedGaussianReal (x : V) : ℝ :=
  (∏ v, Real.exp (-(π * |aR v| * x.1 v ^ 2))) * ∏ v, Real.exp (-(2 * π * ‖aC v‖ * ‖x.2 v‖ ^ 2))

lemma mixedGaussianReal_pos (x : V) : 0 < mixedGaussianReal aR aC x := by
  unfold mixedGaussianReal
  exact mul_pos (Finset.prod_pos fun v _ => Real.exp_pos _)
    (Finset.prod_pos fun v _ => Real.exp_pos _)

lemma mixedGaussian_zero_zero (x : V) :
    mixedGaussian aR aC 0 0 x = (mixedGaussianReal aR aC x : ℂ) := by
  simp only [mixedGaussian, mixedGaussianReal, realGaussian, complexGaussian, Pi.zero_apply,
    Fin.val_zero, Int.toNat_zero, neg_zero, pow_zero, one_mul, ofReal_mul, ofReal_prod,
    ofReal_exp, ofReal_neg, ofReal_pow, ofReal_ofNat]

variable {aR aC}

lemma mixedGaussianConst_pos (haR : ∀ v, aR v ≠ 0) (haC : ∀ v, aC v ≠ 0) :
    0 < mixedGaussianConst aR aC := by
  unfold mixedGaussianConst
  refine mul_pos (Finset.prod_pos fun v _ => Real.sqrt_pos.mpr (abs_pos.mpr (haR v)))
    (Finset.prod_pos fun v _ => ?_)
  have := norm_pos_iff.mpr (haC v)
  positivity

lemma mixedGaussianFTConst_zero_zero :
    mixedGaussianFTConst aR aC 0 0 = ((mixedGaussianConst aR aC)⁻¹ : ℝ) := by
  simp only [mixedGaussianFTConst, mixedGaussianConst, Pi.zero_apply, Fin.val_zero,
    Int.natAbs_zero, pow_zero, zpow_zero, mul_one, mul_inv, ← Finset.prod_inv_distrib,
    ofReal_mul, ofReal_prod]

/-- The plain Gaussian is its own Fourier transform up to the constant `κ⁻¹`. -/
theorem fourierIntegral_mixedGaussian_zero_zero (haR : ∀ v, aR v ≠ 0) (haC : ∀ v, aC v ≠ 0)
    (w : V) :
    VectorFourier.fourierIntegral 𝐞 volume (tracePairing aR aC) (mixedGaussian aR aC 0 0) w =
      ((mixedGaussianConst aR aC)⁻¹ : ℝ) * mixedGaussian aR aC 0 0 w := by
  rw [fourierIntegral_mixedGaussian 0 0 haR haC, neg_zero, mixedGaussianFTConst_zero_zero]

/-- **Covolume duality.** For a basis `b` of the mixed space and its dual basis `b^*` for the
trace pairing (`tracePairing (b i) (b^* j) = δ i j`), `vol(b) vol(b^*) κ² = 1`, where
`κ = ∏ √|aR v| ∏ 2 |aC v|` and the volumes are Lebesgue volumes of the parallelepipeds. The
proof applies Poisson summation twice to the plain Gaussian. -/
theorem measureReal_parallelepiped_mul_dualBasis (haR : ∀ v, aR v ≠ 0) (haC : ∀ v, aC v ≠ 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ V) :
    volume.real (parallelepiped b) *
        volume.real (parallelepiped ((tracePairing aR aC).flip.dualBasis
          (tracePairing_nondegenerate haR haC).flip b)) *
      mixedGaussianConst aR aC ^ 2 = 1 := by
  set B := tracePairing aR aC
  have hB : B.Nondegenerate := tracePairing_nondegenerate haR haC
  set b' := B.flip.dualBasis hB.flip b
  have hb'' : B.flip.dualBasis hB.flip b' = b :=
    LinearMap.BilinForm.dualBasis_dualBasis hB.flip (tracePairing_flip_isSymm aR aC) b
  let G : C(V, ℂ) := ⟨mixedGaussian aR aC 0 0, continuous_mixedGaussian aR aC 0 0⟩
  have hG : ∀ x, G x = (mixedGaussianReal aR aC x : ℂ) := mixedGaussian_zero_zero aR aC
  set κ := mixedGaussianConst aR aC
  have hκ : 0 < κ := mixedGaussianConst_pos haR haC
  have hr : (finrank ℝ V : ℝ) < finrank ℝ V + 1 := by linarith
  obtain ⟨C, hC⟩ := exists_norm_mixedGaussian_le_rpow 0 0 haR haC (finrank ℝ V + 1)
  have hFT : ∀ w, VectorFourier.fourierIntegral 𝐞 volume B G w = ((κ⁻¹ : ℝ) : ℂ) * G w :=
    fourierIntegral_mixedGaussian_zero_zero haR haC
  have hsum : ∀ c : Basis ι ℝ V, Summable fun n => G (latticeVec c n) := fun c => by
    have h := summable_add_latticeVec_of_decay c hr hC 0
    simp only [zero_add] at h
    exact h
  have hP : ∀ c : Basis ι ℝ V, ∑' n, G (latticeVec c n) =
      (((volume.real (parallelepiped c))⁻¹ : ℝ) : ℂ) * ((κ⁻¹ : ℝ) : ℂ) *
        ∑' m, G (latticeVec (B.flip.dualBasis hB.flip c) m) := by
    intro c
    have h := tsum_add_latticeVec_eq volume hB c G hr hC
      (by simp_rw [hFT]; exact (hsum _).mul_left _) 0
    simp only [zero_add, map_zero, LinearMap.zero_apply, AddChar.map_zero_eq_one, Circle.coe_one,
      mul_one, hFT] at h
    rw [h, tsum_mul_left, mul_assoc]
  have hvol : ∀ c : Basis ι ℝ V, (volume.real (parallelepiped c) : ℂ) ≠ 0 := fun c =>
    ofReal_ne_zero.mpr (measureReal_parallelepiped_pos volume c).ne'
  have hκ' : ((κ⁻¹ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (inv_ne_zero hκ.ne')
  have h1 := hP b
  have h2 := hP b'
  rw [hb''] at h2
  set S := ∑' n, G (latticeVec b n)
  set S' := ∑' m, G (latticeVec b' m)
  have hS : S ≠ 0 := by
    have hs : Summable fun n => mixedGaussianReal aR aC (latticeVec b n) :=
      summable_ofReal.mp (by simpa only [hG] using hsum b)
    have : S = ((∑' n, mixedGaussianReal aR aC (latticeVec b n) : ℝ) : ℂ) := by
      simp only [S, hG, ofReal_tsum]
    rw [this, ofReal_ne_zero]
    exact (hs.tsum_pos (fun n => (mixedGaussianReal_pos aR aC _).le) 0
      (mixedGaussianReal_pos aR aC _)).ne'
  have hvb := hvol b
  have hvb' := hvol b'
  have hκc : (κ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hκ.ne'
  have e : S = ((volume.real (parallelepiped b) : ℂ))⁻¹ * (κ : ℂ)⁻¹ *
      (((volume.real (parallelepiped b') : ℂ))⁻¹ * (κ : ℂ)⁻¹ * S) := by
    conv_lhs => rw [h1, h2]
    simp only [ofReal_inv]
  have key : ((volume.real (parallelepiped b) * volume.real (parallelepiped b') * κ ^ 2 : ℝ) : ℂ)
      * S = 1 * S := by
    conv_lhs => rw [e]
    push_cast
    field_simp
  exact_mod_cast mul_right_cancel₀ hS key

end Covolume

end Langlands.Global.Hecke

end
