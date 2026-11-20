import Langlands.Representation.Archimedean.RealSmallOrthogonalHaar
import Langlands.Representation.Archimedean.RealBlockFourierFinite
import Langlands.Representation.Archimedean.RealBlockFourierPropagation

/-! # Sign and low-mode averages as weighted orthogonal Haar integrals -/

noncomputable section

set_option autoImplicit false

open Matrix MeasureTheory
open scoped Matrix.Norms.Operator

namespace Langlands.Archimedean.RealSmallOrthogonalFourier

open RealSmallOrthogonalHaar RealBlockFourierFinite RealBlockPropagation

local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ

/-- The weight with value one on determinant one and value `ε` on determinant minus one. -/
def determinantWeight {n : ℕ} (ε : ℂ) : C(K n, ℂ) where
  toFun k := (1 + ε) / 2 + (1 - ε) / 2 * (k.val.det : ℂ)
  continuous_toFun := continuous_const.add (continuous_const.mul
    (Complex.continuous_ofReal.comp continuous_subtype_val.matrix_det))

theorem determinantWeight_of_det_one {n : ℕ} (ε : ℂ) {k : K n} (hk : k.val.det = 1) :
    determinantWeight ε k = 1 := by
  change (1 + ε) / 2 + (1 - ε) / 2 * (k.val.det : ℂ) = 1
  rw [hk, Complex.ofReal_one]
  ring

theorem determinantWeight_of_det_neg_one {n : ℕ} (ε : ℂ) {k : K n}
    (hk : k.val.det = -1) : determinantWeight ε k = ε := by
  change (1 + ε) / 2 + (1 - ε) / 2 * (k.val.det : ℂ) = ε
  rw [hk, Complex.ofReal_neg, Complex.ofReal_one]
  ring

/-- The signed average on one real coordinate as a weighted Haar integral. -/
theorem integral_determinantWeight_one (μ : Measure (K 1)) [μ.IsHaarMeasure]
    [IsProbabilityMeasure μ] (ε : ℂ) (f : C(K 1, ℂ)) :
    (∫ k, determinantWeight ε k * f k ∂μ) = (f 1 + ε * f signOne) / 2 := by
  have h₁ : (1 : K 1).val.det = 1 := Matrix.det_one
  have hs : signOne.val.det = -1 := by
    change (diagonal fun i : Fin 1 => if i = 0 then (-1 : ℝ) else 1).det = -1
    simp
  have he := integral_orthogonal_one μ (determinantWeight ε * f)
  change (∫ k, determinantWeight ε k * f k ∂μ) =
    (determinantWeight ε 1 * f 1 + determinantWeight ε signOne * f signOne) / 2 at he
  rw [determinantWeight_of_det_one ε h₁, one_mul, determinantWeight_of_det_neg_one ε hs] at he
  exact he

private theorem det_rotation (θ : ℝ) : (rotation θ).val.det = 1 := by
  rw [rotation_val, Matrix.det_fin_two]
  change Real.cos θ * Real.cos θ - (-Real.sin θ) * Real.sin θ = 1
  nlinarith [Real.sin_sq_add_cos_sq θ]

private theorem det_reflection : reflectTwo.val.det = -1 := by
  change (diagonal fun i : Fin 2 => if i = 0 then (-1 : ℝ) else 1).det = -1
  simp

private theorem det_left_reflected_rotation (θ : ℝ) : (reflectTwo * rotation θ).val.det = -1 := by
  change (reflectTwo.val * (rotation θ).val).det = -1
  rw [det_mul, det_reflection, det_rotation, mul_one]

private theorem right_reflected_rotation (θ : ℝ) :
    rotation θ * reflectTwo = reflectTwo * rotation (-θ) := by
  have he : reflectTwo * rotation (-θ) * reflectTwo = rotation θ := by
    have h := RealBlockRotation.signReflection_mul_blockRotation_mul_of_mem
      (by decide : 0 + 1 < 2) (0 : Fin 2) (.inl rfl) (-θ)
    rw [neg_neg] at h
    exact Subtype.ext (congrArg Units.val h)
  rw [← he, mul_assoc (reflectTwo * rotation (-θ)), signReflection_mul_self, mul_one]

private theorem integral_orthogonal_two_left (μ : Measure (K 2)) [μ.IsHaarMeasure]
    [IsProbabilityMeasure μ] (f : C(K 2, ℂ)) :
    (∫ k, f k ∂μ) =
      ((∫ θ in 0..2 * Real.pi, f (rotation θ)) +
        (∫ θ in 0..2 * Real.pi, f (reflectTwo * rotation θ))) / (4 * (Real.pi : ℂ)) := by
  rw [integral_orthogonal_two μ f]
  congr 2
  simp_rw [right_reflected_rotation]
  let g (θ : ℝ) := f (reflectTwo * rotation θ)
  have hg : Function.Periodic g (2 * Real.pi) := by
    intro θ
    exact congrArg (fun k => f (reflectTwo * k)) (rotation_periodic θ)
  change (∫ θ in 0..2 * Real.pi, g (-θ)) = ∫ θ in 0..2 * Real.pi, g θ
  rw [intervalIntegral.integral_comp_neg, neg_zero]
  simpa only [neg_add_cancel, zero_add] using hg.intervalIntegral_add_eq (-(2 * Real.pi)) 0

/-- The phase read from the second row of an orthogonal matrix. -/
def phase : C(K 2, ℂ) where
  toFun k := (k.val 1 1 : ℂ) + (k.val 1 0 : ℂ) * Complex.I
  continuous_toFun := (Complex.continuous_ofReal.comp (continuous_subtype_val.matrix_elem 1 1)).add
    ((Complex.continuous_ofReal.comp (continuous_subtype_val.matrix_elem 1 0)).mul continuous_const)

private lemma phase_ne_zero (k : K 2) : phase k ≠ 0 := by
  intro h
  have h₁ : k.val 1 1 = 0 := by simpa [phase, Complex.add_re, Complex.mul_re] using congrArg Complex.re h
  have h₀ : k.val 1 0 = 0 := by simpa [phase, Complex.add_im, Complex.mul_im] using congrArg Complex.im h
  have hk := (mem_orthogonalGroup_iff (Fin 2) ℝ).mp k.2
  have he := congrArg (fun A : M 2 => A 1 1) hk
  simp [Matrix.mul_apply, Fin.sum_univ_two, h₁, h₀] at he

@[simp]
theorem phase_rotation (θ : ℝ) : phase (rotation θ) = Complex.exp ((θ : ℂ) * Complex.I) := by
  change ((rotation θ).val 1 1 : ℂ) + ((rotation θ).val 1 0 : ℂ) * Complex.I = _
  rw [rotation_val, Complex.exp_ofReal_mul_I]
  rfl

@[simp]
theorem phase_left_reflected_rotation (θ : ℝ) :
    phase (reflectTwo * rotation θ) = Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [← phase_rotation]
  change ((reflectTwo.val * (rotation θ).val) 1 1 : ℂ) +
      ((reflectTwo.val * (rotation θ).val) 1 0 : ℂ) * Complex.I = _
  simp [phase, signReflection_val, Matrix.diagonal_mul]

private def phaseCoefficient (j : ℤ) : C(K 2, ℂ) where
  toFun k := phase k ^ (-j)
  continuous_toFun := phase.continuous.zpow₀ _ fun k => .inl (phase_ne_zero k)

private theorem phaseCoefficient_of_phase {k : K 2} {θ : ℝ}
    (hk : phase k = Complex.exp ((θ : ℂ) * Complex.I)) (j : ℤ) :
    phaseCoefficient j k = Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) := by
  change phase k ^ (-j) = _
  rw [hk, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/-- The sign on the first coordinate of an induced block of weight magnitude `m`. -/
def inducedSign (m : ℕ) : ℂ := (-1 : ℂ) ^ ((m : ℤ) + 1)

theorem inducedSign_eq_pow (m : ℕ) : inducedSign m = (-1 : ℂ) ^ (m + 1) := by
  change (-1 : ℂ) ^ ((m + 1 : ℕ) : ℤ) = _
  exact zpow_natCast (-1 : ℂ) (m + 1)

/-- The four-sign average with induced first sign and trivial second sign. -/
def pairSignAverage (m : ℕ) (f : C(K 2, ℂ)) (k : K 2) : ℂ :=
  (f k + inducedSign m * f (reflectTwo * k) + f (signReflection 2 1 * k) +
    inducedSign m * f (reflectTwo * signReflection 2 1 * k)) / 4

/-- The continuous weight for the sign and low-mode average on an induced block. -/
def pairDensity (m : ℕ) : C(K 2, ℂ) :=
  determinantWeight (inducedSign m) * ∑ j ∈ window m, phaseCoefficient j

private theorem rotation_pi : rotation Real.pi = reflectTwo * signReflection 2 1 :=
  Subtype.ext (congrArg Units.val (RealBlockRotation.blockRotation_pi (by decide : 0 + 1 < 2)))

private theorem pair_signs_rotation (θ : ℝ) :
    reflectTwo * signReflection 2 1 * rotation θ = rotation (θ + Real.pi) := by
  rw [← rotation_pi, ← rotation_add, add_comm]

private theorem second_sign_rotation (θ : ℝ) :
    signReflection 2 1 * rotation θ = reflectTwo * rotation (θ + Real.pi) := by
  rw [← pair_signs_rotation, ← mul_assoc, ← mul_assoc reflectTwo reflectTwo,
    signReflection_mul_self, one_mul]

private theorem expMode_pi (j : ℤ) : expMode j Real.pi = (-1 : ℂ) ^ j := by
  rw [expMode, mul_assoc, Complex.exp_int_mul, Complex.exp_pi_mul_I]

private theorem pairSignAverage_coeff (m : ℕ) (f : C(K 2, ℂ)) (j : ℤ) :
    coeff j (fun θ => pairSignAverage m f (rotation θ)) =
      if Even (j + (m : ℤ) + 1) then
        (coeff j (fun θ => f (rotation θ)) +
          inducedSign m * coeff j (fun θ => f (reflectTwo * rotation θ))) / 2
      else 0 := by
  let F (θ : ℝ) := f (rotation θ)
  let E (θ : ℝ) := f (reflectTwo * rotation θ)
  let ε := inducedSign m
  let Fπ (θ : ℝ) := F (θ + Real.pi)
  let Eπ (θ : ℝ) := E (θ + Real.pi)
  have hF : Continuous F := f.continuous.comp continuous_rotation
  have hE : Continuous E := f.continuous.comp (continuous_const.mul continuous_rotation)
  have hFπ : Continuous Fπ := hF.comp (continuous_id.add continuous_const)
  have hEπ : Continuous Eπ := hE.comp (continuous_id.add continuous_const)
  have hPF : Function.Periodic F (2 * Real.pi) := fun θ => congrArg f (rotation_periodic θ)
  have hPE : Function.Periodic E (2 * Real.pi) :=
    fun θ => congrArg (fun k => f (reflectTwo * k)) (rotation_periodic θ)
  have havg : (fun θ => pairSignAverage m f (rotation θ)) =
      (4 : ℂ)⁻¹ • (F + ε • E + Eπ + ε • Fπ) := by
    funext θ
    simp only [pairSignAverage, pair_signs_rotation, second_sign_rotation, Pi.smul_apply,
      Pi.add_apply, smul_eq_mul, F, E, Fπ, Eπ, ε]
    ring
  change _ = if Even (j + (m : ℤ) + 1) then (coeff j F + ε * coeff j E) / 2 else 0
  rw [havg, coeff_smul,
    coeff_add ((hF.add (hE.const_smul ε)).add hEπ) (hFπ.const_smul ε),
    coeff_add (hF.add (hE.const_smul ε)) hEπ, coeff_add hF (hE.const_smul ε),
    coeff_smul, coeff_smul]
  have heπ : coeff j Eπ = expMode j Real.pi * coeff j E := coeff_comp_add hPE j Real.pi
  have hfπ : coeff j Fπ = expMode j Real.pi * coeff j F := coeff_comp_add hPF j Real.pi
  rw [heπ, hfπ, expMode_pi]
  let u := (-1 : ℂ) ^ j
  have hε : ε * ε = 1 := by
    change (-1 : ℂ) ^ ((m : ℤ) + 1) * (-1 : ℂ) ^ ((m : ℤ) + 1) = 1
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    exact (show Even (((m : ℤ) + 1) + ((m : ℤ) + 1)) from ⟨(m : ℤ) + 1, rfl⟩).neg_one_zpow
  have hfac : ε + u = (1 + ε * u) * ε := by
    rw [add_mul, one_mul, mul_comm ε u, mul_assoc, hε, mul_one]
  have hsign : ε * u = (-1 : ℂ) ^ (j + (m : ℤ) + 1) := by
    change (-1 : ℂ) ^ ((m : ℤ) + 1) * (-1 : ℂ) ^ j = _
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    congr 1
    omega
  calc
    _ = (4 : ℂ)⁻¹ * ((1 + ε * u) * coeff j F + (ε + u) * coeff j E) := by
      change (4 : ℂ)⁻¹ * (coeff j F + ε * coeff j E + u * coeff j E +
        ε * (u * coeff j F)) = _
      ring
    _ = (4 : ℂ)⁻¹ * ((1 + ε * u) * (coeff j F + ε * coeff j E)) := by rw [hfac]; ring
    _ = _ := by
      rw [hsign]
      split_ifs with hj
      · rw [hj.neg_one_zpow]
        ring
      · rw [(Int.not_even_iff_odd.mp hj).neg_one_zpow]
        ring

private theorem integral_phaseCoefficient (μ : Measure (K 2)) [μ.IsHaarMeasure]
    [IsProbabilityMeasure μ] (ε : ℂ) (f : C(K 2, ℂ)) (j : ℤ) :
    (∫ k, determinantWeight ε k * phaseCoefficient j k * f k ∂μ) =
      (coeff j (fun θ => f (rotation θ)) + ε * coeff j (fun θ => f (reflectTwo * rotation θ))) /
        (4 * (Real.pi : ℂ)) := by
  let F : C(K 2, ℂ) := determinantWeight ε * phaseCoefficient j * f
  change (∫ k, F k ∂μ) = _
  rw [integral_orthogonal_two_left μ F]
  change ((∫ θ in 0..2 * Real.pi,
      determinantWeight ε (rotation θ) * phaseCoefficient j (rotation θ) * f (rotation θ)) +
    (∫ θ in 0..2 * Real.pi, determinantWeight ε (reflectTwo * rotation θ) *
      phaseCoefficient j (reflectTwo * rotation θ) * f (reflectTwo * rotation θ))) /
        (4 * (Real.pi : ℂ)) = _
  simp only [determinantWeight_of_det_one ε (det_rotation _), one_mul,
    determinantWeight_of_det_neg_one ε (det_left_reflected_rotation _),
    phaseCoefficient_of_phase (phase_rotation _) j,
    phaseCoefficient_of_phase (phase_left_reflected_rotation _) j]
  congr 2
  · unfold coeff
    apply intervalIntegral.integral_congr
    intro θ _
    exact mul_comm _ _
  · unfold coeff
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    ring

private theorem normalized_pairSignAverage_coeff (μ : Measure (K 2)) [μ.IsHaarMeasure]
    [IsProbabilityMeasure μ] (m : ℕ) (f : C(K 2, ℂ)) (j : ℤ) :
    (2 * (Real.pi : ℂ))⁻¹ * coeff j (fun θ => pairSignAverage m f (rotation θ)) =
      if Even (j + (m : ℤ) + 1) then
        ∫ k, determinantWeight (inducedSign m) k * phaseCoefficient j k * f k ∂μ
      else 0 := by
  rw [pairSignAverage_coeff, integral_phaseCoefficient]
  split_ifs
  · ring
  · rw [mul_zero]

/-- The normalized low-mode rotation average after the two sign filters is the weighted
probability Haar integral on the whole orthogonal block. -/
theorem integral_pairDensity (μ : Measure (K 2)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (m : ℕ) (f : C(K 2, ℂ)) :
    (2 * (Real.pi : ℂ))⁻¹ *
        (∑ j ∈ Finset.Ioo (-(m : ℤ)) m, coeff j (fun θ => pairSignAverage m f (rotation θ))) =
      ∫ k, pairDensity m k * f k ∂μ := by
  calc
    _ = ∑ j ∈ window m, ∫ k, determinantWeight (inducedSign m) k * phaseCoefficient j k * f k ∂μ := by
      rw [Finset.mul_sum, window, Finset.sum_filter]
      exact Finset.sum_congr rfl fun j _ => normalized_pairSignAverage_coeff μ m f j
    _ = _ := by
      rw [← integral_finsetSum]
      · apply integral_congr_ae
        filter_upwards with k
        simp only [pairDensity, ContinuousMap.mul_apply, ContinuousMap.sum_apply,
          Finset.mul_sum, Finset.sum_mul]
      · intro j _
        let F : C(K 2, ℂ) := determinantWeight (inducedSign m) * phaseCoefficient j * f
        exact F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem neg_mem_window {m : ℕ} {j : ℤ} (hj : j ∈ window m) : -j ∈ window m := by
  rw [mem_window, abs_neg]
  obtain ⟨ha, k, hk⟩ := mem_window.mp hj
  exact ⟨ha, k - j, by omega⟩

private theorem sum_neg_expMode (m : ℕ) (θ : ℝ) :
    (∑ j ∈ window m, expMode (-j) θ) = ∑ j ∈ window m, expMode j θ := by
  refine Finset.sum_nbij' Neg.neg Neg.neg (fun j => neg_mem_window) (fun j => neg_mem_window)
    (fun j _ => neg_neg j) (fun j _ => neg_neg j) (fun _ _ => rfl)

/-- The induced block weight at a rotation is the parity-window sum. -/
theorem pairDensity_rotation (m : ℕ) (θ : ℝ) :
    pairDensity m (rotation θ) = ∑ j ∈ window m, expMode j θ := by
  rw [← sum_neg_expMode]
  simp only [pairDensity, ContinuousMap.mul_apply, ContinuousMap.sum_apply,
    determinantWeight_of_det_one (inducedSign m) (det_rotation θ), one_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [phaseCoefficient_of_phase (phase_rotation θ), expMode]
  congr 1
  push_cast
  ring

/-- Reversing the angular orientation preserves the parity-window value. -/
theorem pairDensity_rotation_neg (m : ℕ) (θ : ℝ) :
    pairDensity m (rotation (-θ)) = ∑ j ∈ window m, expMode j θ := by
  rw [pairDensity_rotation, ← sum_neg_expMode]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold expMode
  congr 1
  push_cast
  ring

/-- Conjugating the inverse rotation by an orthogonal frame keeps the same window sum. -/
theorem pairDensity_conj_inv_rotation (m : ℕ) (θ : ℝ) (k : K 2) :
    pairDensity m (k * (rotation θ)⁻¹ * k⁻¹) = ∑ j ∈ window m, expMode j θ := by
  have hinv : rotation (-θ) = (rotation θ)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← rotation_add, neg_add_cancel]
    exact Subtype.ext (congrArg Units.val (RealBlockRotation.blockRotation_zero 2 0))
  have hcomm (a b : ℝ) : rotation a * rotation b = rotation b * rotation a := by
    rw [← rotation_add, ← rotation_add, add_comm]
  rw [← hinv]
  obtain ⟨a, rfl | rfl⟩ := orthogonal_two_cases k
  · rw [hcomm a (-θ), mul_inv_cancel_right, pairDensity_rotation_neg]
  · have hrel : (rotation a * reflectTwo) * rotation (-θ) =
        rotation θ * (rotation a * reflectTwo) := by
      rw [mul_assoc, ← right_reflected_rotation θ, ← mul_assoc, hcomm a θ, mul_assoc]
    rw [hrel, mul_inv_cancel_right, pairDensity_rotation]

/-- The local sign and low-mode filters have continuous Haar weights, with a common
angular value at either orientation of a rotation. -/
def RealSmallOrthogonalFourierStatement : Prop :=
  (∀ (μ : Measure (K 1)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] (ε : ℂ) (f : C(K 1, ℂ)),
    (∫ k, determinantWeight ε k * f k ∂μ) = (f 1 + ε * f signOne) / 2) ∧
  (∀ (μ : Measure (K 2)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] (m : ℕ) (f : C(K 2, ℂ)),
    (2 * (Real.pi : ℂ))⁻¹ *
        (∑ j ∈ Finset.Ioo (-(m : ℤ)) m, coeff j (fun θ => pairSignAverage m f (rotation θ))) =
      ∫ k, pairDensity m k * f k ∂μ) ∧
  ∀ (m : ℕ) (θ : ℝ),
    pairDensity m (rotation θ) = ∑ j ∈ window m, expMode j θ ∧
    pairDensity m (rotation (-θ)) = ∑ j ∈ window m, expMode j θ

theorem realSmallOrthogonalFourier : RealSmallOrthogonalFourierStatement :=
  ⟨integral_determinantWeight_one, integral_pairDensity,
    fun m θ => ⟨pairDensity_rotation m θ, pairDensity_rotation_neg m θ⟩⟩

end Langlands.Archimedean.RealSmallOrthogonalFourier
