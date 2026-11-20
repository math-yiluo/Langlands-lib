import Langlands.Analysis.CompactWeightedIntegral
import Langlands.HarmonicAnalysis.TorusFourierInversion

/-! # Factorization of a compact kernel by a smooth torus extension -/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

set_option autoImplicit false

namespace Langlands.Analysis

open Langlands.Plancherel Langlands.HarmonicAnalysis.TorusFourier

variable {J : Type*} [Fintype J] [DecidableEq J]
  {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [CompactSpace Y]

local notation "T" => J → Circle
local notation "Z" => J → ℤ

variable (μ : Measure (J → Circle)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
  (P : C((J → Circle) × Y, ℂ)) (p : C(X, J → Circle))

/-- The Fourier coefficient of a continuous torus kernel as a continuous profile
in its other variable. -/
def kernelFourierCoeff (m : Z) : C(Y, ℂ) :=
  ∫ z, torusCharacter m z • P.curry z ∂μ

omit [DecidableEq J] [μ.IsMulLeftInvariant] in
private theorem kernelFourierCoeff_apply (m : Z) (y : Y) :
    kernelFourierCoeff μ P m y = torusFourierCoeff μ (fun z => P (z, y)) m := by
  have hI : Integrable (fun z => torusCharacter m z • P.curry z) μ :=
    ((continuous_torusCharacter m).smul P.curry.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [kernelFourierCoeff, ContinuousMap.integral_apply hI]
  simp only [ContinuousMap.smul_apply, ContinuousMap.curry_apply, smul_eq_mul, torusFourierCoeff, mul_comm]

private def fourierWeight (m : Z) : ℝ :=
  ∏ j, ((1 + |(m j : ℝ)|) ^ 2)⁻¹

omit [DecidableEq J] in
private theorem fourierWeight_pos (m : Z) : 0 < fourierWeight m :=
  Finset.prod_pos (fun j _ => by positivity)

private theorem norm_kernelFourierCoeff_le {M : ℝ} (hM : 0 ≤ M)
    (hP : ∀ y : Y, IsSmoothFiniteTorusFunction (fun z => P (z, y)))
    (hval : ∀ z y, ‖P (z, y)‖ ≤ M)
    (hder : ∀ j z y, ‖(torusPartialDeriv j)^[4 * Fintype.card J] (fun z => P (z, y)) z‖ ≤ M)
    (m : Z) (y : Y) :
    ‖kernelFourierCoeff μ P m y‖ ≤ (2 ^ (4 * Fintype.card J) * (1 + Fintype.card J) * M) *
      (fourierWeight m) ^ 2 := by
  let k := 4 * Fintype.card J
  let C : ℝ := 2 ^ k * (1 + Fintype.card J) * M
  let D : ℝ := ∏ j, (1 + |(m j : ℝ)|) ^ 2
  have hC : 0 ≤ C := by positivity
  have hD : 0 < D := Finset.prod_pos (fun j _ => by positivity)
  have hweight : fourierWeight m = D⁻¹ := Finset.prod_inv_distrib ..
  have hpow : D ^ 2 ≤ (1 + ‖m‖) ^ k := by
    have h := Finset.prod_le_prod₀ (s := Finset.univ)
      (f := fun j : J => (1 + |(m j : ℝ)|) ^ 2) (g := fun _ => (1 + ‖m‖) ^ 2)
      (fun j _ => by positivity) fun j _ => by
        have hnorm := norm_le_pi_norm m j
        rw [Int.norm_eq_abs] at hnorm
        exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hle : D ≤ (1 + ‖m‖) ^ (2 * Fintype.card J) := by
      simpa only [D, Finset.prod_const, Finset.card_univ, ← pow_mul] using h
    have hsq := pow_le_pow_left₀ hD.le hle 2
    rw [← pow_mul, show 2 * Fintype.card J * 2 = k by dsimp [k]; omega] at hsq
    exact hsq
  rw [kernelFourierCoeff_apply]
  have hr := one_add_norm_pow_mul_norm_torusFourierCoeff_le μ (hP y) k
    (fun z => hval z y) (fun j z => hder j z y) m
  have hb : (1 + ‖m‖) ^ k * ‖torusFourierCoeff μ (fun z => P (z, y)) m‖ ≤ C := by
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one, C] using hr
  calc
    _ ≤ C / (1 + ‖m‖) ^ k := (le_div_iff₀ (by positivity)).2 (by rwa [mul_comm])
    _ ≤ C / D ^ 2 := div_le_div_of_nonneg_left hC (by positivity) hpow
    _ = _ := by rw [hweight, inv_pow, div_eq_mul_inv]

private def leftKernelTerm (m : Z) : C(X × T, ℂ) :=
  ⟨fun xz => (fourierWeight m : ℂ) * conj (torusCharacter m (p xz.1)) * torusCharacter m xz.2,
    (continuous_const.mul (Complex.continuous_conj.comp
      ((continuous_torusCharacter m).comp (p.continuous.comp continuous_fst)))).mul
        ((continuous_torusCharacter m).comp continuous_snd)⟩

private def rightKernelTerm (m : Z) : C(T × Y, ℂ) :=
  ⟨fun zy => kernelFourierCoeff μ P m zy.2 / (fourierWeight m : ℂ) * conj (torusCharacter m zy.1),
    (((kernelFourierCoeff μ P m).continuous.comp continuous_snd).div_const _).mul
      (Complex.continuous_conj.comp ((continuous_torusCharacter m).comp continuous_fst))⟩

set_option maxHeartbeats 600000 in
/-- A compact kernel obtained from a smooth torus family with uniform derivative bounds
factors as a composition of two continuous kernels through the torus. -/
theorem exists_torus_kernel_factorization {M : ℝ} (hM : 0 ≤ M)
    (hP : ∀ y : Y, IsSmoothFiniteTorusFunction (fun z => P (z, y)))
    (hval : ∀ z y, ‖P (z, y)‖ ≤ M)
    (hder : ∀ j z y, ‖(torusPartialDeriv j)^[4 * Fintype.card J] (fun z => P (z, y)) z‖ ≤ M) :
    ∃ (A : C(X × T, ℂ)) (B : C(T × Y, ℂ)),
      ∀ x y, (∫ z, A (x, z) * B (z, y) ∂μ) = P (p x, y) := by
  let C : ℝ := 2 ^ (4 * Fintype.card J) * (1 + Fintype.card J) * M
  let w : Z → ℝ := fourierWeight
  have hC : 0 ≤ C := by positivity
  have hw : Summable w := summable_prod_one_add_abs_sq_inv
  have hw0 (m : Z) : 0 < w m := fourierWeight_pos m
  have hB (m : Z) (y : Y) : ‖kernelFourierCoeff μ P m y / (w m : ℂ)‖ ≤ C * w m := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hw0 m).le, div_le_iff₀ (hw0 m)]
    rw [mul_assoc, ← pow_two]
    exact norm_kernelFourierCoeff_le μ P hM hP hval hder m y
  have hAL (m : Z) : ‖leftKernelTerm p m‖ ≤ w m := by
    apply (ContinuousMap.norm_le _ (hw0 m).le).mpr
    intro xz
    change ‖(w m : ℂ) * conj (torusCharacter m (p xz.1)) * torusCharacter m xz.2‖ ≤ w m
    simp [norm_torusCharacter, Real.norm_of_nonneg (hw0 m).le]
  have hBL (m : Z) : ‖rightKernelTerm μ P m‖ ≤ C * w m := by
    apply (ContinuousMap.norm_le _ (mul_nonneg hC (hw0 m).le)).mpr
    intro zy
    change ‖kernelFourierCoeff μ P m zy.2 / (w m : ℂ) * conj (torusCharacter m zy.1)‖ ≤ C * w m
    simpa only [norm_mul, RCLike.norm_conj, norm_torusCharacter, mul_one] using hB m zy.2
  have hASum : Summable (leftKernelTerm p) :=
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hAL hw).of_norm
  have hBSum : Summable (rightKernelTerm μ P) :=
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hBL (hw.mul_left C)).of_norm
  let A := ∑' m, leftKernelTerm p m
  let B := ∑' m, rightKernelTerm μ P m
  refine ⟨A, B, ?_⟩
  intro x y
  let B₀ : C(T, ℂ) := B.comp ⟨fun z => (z, y), continuous_id.prodMk continuous_const⟩
  have hBy (z : T) : B (z, y) = ∑' m, (kernelFourierCoeff μ P m y / (w m : ℂ)) *
      conj (torusCharacter m z) := by
    exact (ContinuousMap.evalCLM ℂ (M := ℂ) (z, y)).map_tsum hBSum
  have hCoeff (m : Z) : torusFourierCoeff μ B₀ m = kernelFourierCoeff μ P m y / (w m : ℂ) := by
    have hsum : Summable fun m : Z => ‖kernelFourierCoeff μ P m y / (w m : ℂ)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => hB m y) (hw.mul_left C)
    have he : (B₀ : T → ℂ) = fun z => ∑' m, (kernelFourierCoeff μ P m y / (w m : ℂ)) *
      conj (torusCharacter m z) := funext hBy
    rw [he, torusFourierCoeff_tsum μ hsum, Measure.real, measure_univ, ENNReal.toReal_one,
      Complex.ofReal_one, one_mul]
  let i : C(T, X × T) := ⟨fun z => (x, z), continuous_const.prodMk continuous_id⟩
  let L := (compactWeightedIntegral μ B₀).comp (ContinuousMap.compCLM ℂ ℂ i)
  have hL (m : Z) : L (leftKernelTerm p m) = kernelFourierCoeff μ P m y *
      conj (torusCharacter m (p x)) := by
    change (∫ z, ((w m : ℂ) * conj (torusCharacter m (p x)) * torusCharacter m z) * B₀ z ∂μ) = _
    calc
      _ = ((w m : ℂ) * conj (torusCharacter m (p x))) * torusFourierCoeff μ B₀ m := by
        rw [torusFourierCoeff, ← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by ring
      _ = _ := by
        rw [hCoeff]
        have hne : (w m : ℂ) ≠ 0 := by exact_mod_cast (hw0 m).ne'
        field_simp
  change L A = P (p x, y)
  calc
    _ = ∑' m, L (leftKernelTerm p m) := L.map_tsum hASum
    _ = _ := by
      simp_rw [hL, kernelFourierCoeff_apply]
      exact (hasSum_torusFourierCoeff_mul_conj_of_isProbabilityMeasure μ (hP y).continuous
        (summable_norm_torusFourierCoeff μ (hP y)) (p x)).tsum_eq

end Langlands.Analysis
