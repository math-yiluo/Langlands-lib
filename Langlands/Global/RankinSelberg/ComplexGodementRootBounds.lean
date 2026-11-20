import Langlands.Global.RankinSelberg.ComplexGodementRootDerivatives

/-! # Uniform logarithmic root estimates for continued Godement values -/

noncomputable section

open MeasureTheory Set
open scoped Classical Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementRootBounds

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (determinant)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure UnitaryAdditiveCharacter)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter)
open ComplexGodement (norm_characterWeight)
open ComplexGodementAddedCharacter (continuedValue rightTest)
open ComplexGodementColumnChange (iteratedKernel)
open ComplexGodementRootDerivatives (rootPath rootPath_zero rootPath_mem rootRatio logTorus_mul_rootPath
  rootFrequency rootFrequency_ne_zero whittakerCharacter_rootPath rootTestDerivative
  determinantFactor iteratedDeriv_continuedValue_rootPath iteratedDeriv_exp_linear_zero)
open ComplexGodementTranslatedBounds (rightTestSize one_le_rightTestSize seminorm_rightTest_le
  complexGodementTranslatedBounds)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexLocalIwasawa (alpha kpart npart npart_mul_logTorus_mul_kpart)
open ComplexLocalOrdinaryConvergence (norm_detPower_logTorus_mul)
open ComplexLocalWhittakerGauge (logTorus logTorus_val logTorus_inv_val)
open RealConvergenceAnalysis (rootPos rootPos_nonneg norm_cexp_mul_ofReal)
open ArchimedeanLocal (complexNormalizedAbs)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "K" => unitaryCompact ℂ (r + 1 + 1)
local notation "Y" => Fin (r + 1 + 1) → ℝ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ
local notation "m" => (r + 1 + 1 : ℕ)

private def logLength (y : Y) : ℝ := ∑ i, |y i|

private theorem logLength_nonneg (y : Y) : 0 ≤ logLength y := Finset.sum_nonneg fun _ _ => abs_nonneg _

private theorem abs_le_logLength (y : Y) (i : Fin m) : |y i| ≤ logLength y :=
  Finset.single_le_sum (f := fun j => |y j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

private theorem rightTestSize_torus_le (y : Y) : rightTestSize (logTorus y) ≤ (m : ℝ) * Real.exp (logLength y) := by
  have hentry (z : Y) (hz : ∀ i, z i ≤ logLength y) :
      ‖Matrix.diagonal (fun i => (Real.exp (z i) : ℂ))‖ ≤ Real.exp (logLength y) := by
    rw [Matrix.norm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (Real.exp_nonneg _)).2
    intro i
    rw [Complex.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_monotone (hz i)
  have hf := hentry y fun i => (le_abs_self _).trans (abs_le_logLength y i)
  have hi := hentry (-y) fun i => (neg_le_abs _).trans (abs_le_logLength y i)
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  unfold rightTestSize
  rw [logTorus_val, logTorus_inv_val]
  exact max_le (one_le_mul_of_one_le_of_one_le hm (Real.one_le_exp_iff.mpr (logLength_nonneg y)))
    (mul_le_mul_of_nonneg_left (max_le hf hi) (by positivity))

private theorem rightTestSize_unitary_le (k : K) : rightTestSize k.val ≤ (m : ℝ) := by
  have h (u : K) : ‖u.val.val‖ ≤ 1 := (Matrix.norm_le_iff zero_le_one).2
    (Langlands.LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup u.2)
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  unfold rightTestSize
  exact max_le hm ((mul_le_mul_of_nonneg_left (max_le (h k) (h k⁻¹)) (by positivity)).trans_eq (mul_one _))

private theorem exists_bound_iterated_test (a : ℂˣ) (Φ : 𝓢(Rect, ℂ)) (I : Finset (ℕ × ℕ))
    (J : ℕ) (i : Fin (r + 1)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ k : K,
      I.sup (schwartzSeminormFamily ℝ Rect ℂ) ((rootTestDerivative a i ^ J) (rightTest k.val Φ)) ≤ C := by
  let p := I.sup (schwartzSeminormFamily ℝ Rect ℂ)
  let D := rootTestDerivative a i ^ J
  let q := p.comp D.toLinearMap
  have hp : Continuous p := Seminorm.continuous_finsetSup fun i _ =>
    (schwartz_withSeminorms ℝ Rect ℂ).continuous_seminorm i
  obtain ⟨L, B, _, hB⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ Rect ℂ) q (hp.comp D.continuous)
  let N := L.sup (fun z => z.1 + z.2)
  let C := (B : ℝ) * ((m : ℝ) ^ N * L.sup (schwartzSeminormFamily ℝ Rect ℂ) Φ)
  refine ⟨C, by dsimp only [C]; positivity, fun k => ?_⟩
  change q (rightTest k.val Φ) ≤ C
  refine (hB _).trans (mul_le_mul_of_nonneg_left ?_ B.coe_nonneg)
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro j hj
  have hjN : j.1 + j.2 ≤ N := Finset.le_sup (f := fun z => z.1 + z.2) hj
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hM : rightTestSize k.val ^ (j.1 + j.2) ≤ (m : ℝ) ^ N :=
    (pow_le_pow_left₀ (zero_le_one.trans (one_le_rightTestSize k.val)) (rightTestSize_unitary_le k) _).trans
      (pow_le_pow_right₀ hm hjN)
  exact (seminorm_rightTest_le j.1 j.2 k.val Φ).trans
    (mul_le_mul hM (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ Rect ℂ) (x := Φ) hj)
      (apply_nonneg _ _) (by positivity))

private def addedShift (r : ℕ) : ℂ := (((r + 1 : ℕ) + 1 : ℂ) / 2)

private def determinantShift (r : ℕ) : ℂ := (((r + 1 : ℕ) : ℂ) / 2)

private def signNorm (r : ℕ) (d : ComplexCharacterData) : ℝ := ‖(d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ)‖

private def determinantOrder (r : ℕ) (d : ComplexCharacterData) (T : ℝ) : ℝ :=
  2 * (|(d.exponent + determinantShift r).re| + (T + |(addedShift r - 1).re|))

private theorem norm_determinantFactor_le (d : ComplexCharacterData) (y : Y) (k : K) (s : ℂ) {T : ℝ}
    (hs : |(addedShift r + s - 1).re| ≤ T) :
    ‖determinantFactor d (logTorus y * k.val) s‖ ≤ signNorm r d * Real.exp (determinantOrder r d T * logLength y) := by
  let g : G' := logTorus y * k.val
  have hdet : Real.log (complexNormalizedAbs g.val.det) = 2 * ∑ i, y i := by
    apply Real.exp_injective
    have h := norm_detPower_logTorus_mul y k 1
    change ‖ArchimedeanLocal.detPower complexNormalizedAbs g 1‖ = _ at h
    rwa [ArchimedeanLocal.detPower, norm_cexp_mul_ofReal, Complex.one_re, one_mul, mul_one] at h
  have hpos : 0 < complexNormalizedAbs g.val.det :=
    pow_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)) 2
  have hχ : ‖ComplexGodement.characterWeight d (determinantShift r) (determinant g)‖ =
      Real.exp ((d.exponent + determinantShift r).re * (2 * ∑ i, y i)) := by
    rw [norm_characterWeight]
    change complexNormalizedAbs g.val.det ^ (d.exponent + determinantShift r).re = _
    rw [Real.rpow_def_of_pos hpos, hdet, mul_comm]
  have hS : |s.re| ≤ T + |(addedShift r - 1).re| := by
    have he : s.re = (addedShift r + s - 1).re - (addedShift r - 1).re := by simp
    rw [he, sub_eq_add_neg]
    exact (abs_add_le _ _).trans (by rw [abs_neg]; exact add_le_add hs le_rfl)
  have hT : 0 ≤ T := (abs_nonneg _).trans hs
  have hc : 2 * |(d.exponent + determinantShift r).re + s.re| ≤ determinantOrder r d T := by
    apply mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add le_rfl hS)) (by norm_num)
  have hsum : |∑ i, y i| ≤ logLength y := Finset.abs_sum_le_sum_abs _ _
  have hsExp : 2 * ((d.exponent + determinantShift r).re + s.re) * (∑ i, y i) ≤
      determinantOrder r d T * logLength y := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    exact mul_le_mul hc hsum (abs_nonneg _) (by unfold determinantOrder; positivity)
  change ‖determinantFactor d g s‖ ≤ _
  unfold determinantFactor
  rw [norm_mul, norm_mul]
  change (signNorm r d * ‖ComplexGodement.characterWeight d (determinantShift r) (determinant g)‖) *
      ‖ArchimedeanLocal.detPower complexNormalizedAbs g s‖ ≤ _
  rw [hχ, show g = logTorus y * k.val from rfl, norm_detPower_logTorus_mul, mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  convert hsExp using 1
  ring

private theorem exists_root_derivative_bounds {P : Type} (ν : Measure G) [ν.IsHaarMeasure]
    (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (d : ComplexCharacterData) (S : Set P) (W : P → G → ℂ)
    (hWc : ∀ p ∈ S, Continuous (W p)) (hWb : HasUniformSimpleRootBound S W)
    (Φ : 𝓢(Rect, ℂ)) (s : P → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (hs : ∀ p ∈ S, |(addedShift r + s p - 1).re| ≤ T) :
    ∃ N : ℕ, ∀ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S, ∀ (y : Y) (k : K) (i : Fin (r + 1)),
      ‖iteratedDeriv J (fun t => continuedValue ν μ d a Φ (W p) (logTorus y * rootPath a i t * k.val) (s p)) 0‖ ≤
        C * Real.exp ((N : ℝ) * logLength y) := by
  obtain ⟨I, N, B, hBi, hB₀, hB⟩ := complexGodementTranslatedBounds ν μ a d S W hWc hWb T hT
  obtain ⟨M, hM⟩ := exists_nat_ge ((N : ℝ) + determinantOrder r d T)
  refine ⟨M, fun J => ?_⟩
  choose C hC using fun i : Fin (r + 1) => exists_bound_iterated_test a Φ I J i
  let R := ∑ i, C i
  let D := signNorm r d * (∫ h, B h ∂ν) * (m : ℝ) ^ N * R
  have hR : 0 ≤ R := Finset.sum_nonneg fun i _ => (hC i).1
  have hInt : 0 ≤ ∫ h, B h ∂ν := integral_nonneg hB₀
  have hD₀ : 0 ≤ D := by dsimp only [D, signNorm]; positivity
  refine ⟨D, hD₀, fun p hp y k i => ?_⟩
  let Ψ := (rootTestDerivative a i ^ J) (rightTest k.val Φ)
  let b := logTorus y
  let z := addedShift r + s p
  have hderiv := iteratedDeriv_continuedValue_rootPath ν μ a d S W hWc hWb p hp Φ (s p) i b k.val J 0
  rw [rootPath_zero, mul_one] at hderiv
  rw [hderiv, norm_mul]
  change ‖determinantFactor d (b * k.val) (s p)‖ *
    ‖∫ h, iteratedKernel (complexScaledCharacter a) μ d (rightTest b Ψ) (W p) z h ∂ν‖ ≤ _
  have hI := (hB p hp z (hs p hp) b Ψ).2.2
  have hΨ : I.sup (schwartzSeminormFamily ℝ Rect ℂ) Ψ ≤ R :=
    ((hC i).2 k).trans (Finset.single_le_sum (fun j _ => (hC j).1) (Finset.mem_univ i))
  have hb : rightTestSize b ^ N ≤ (m : ℝ) ^ N * Real.exp ((N : ℝ) * logLength y) := by
    rw [Real.exp_nat_mul, ← mul_pow]
    exact pow_le_pow_left₀ (zero_le_one.trans (one_le_rightTestSize b)) (rightTestSize_torus_le y) _
  have hI' : ‖∫ h, iteratedKernel (complexScaledCharacter a) μ d (rightTest b Ψ) (W p) z h ∂ν‖ ≤
      ((∫ h, B h ∂ν) * ((m : ℝ) ^ N * Real.exp (N * logLength y))) * R := by
    refine hI.trans (mul_le_mul (mul_le_mul_of_nonneg_left hb hInt) hΨ (apply_nonneg _ _) ?_)
    positivity
  calc
    _ ≤ (signNorm r d * Real.exp (determinantOrder r d T * logLength y)) *
        ((∫ h, B h ∂ν) * ((m : ℝ) ^ N * Real.exp (N * logLength y)) * R) :=
      mul_le_mul (norm_determinantFactor_le d y k (s p) (hs p hp)) hI' (norm_nonneg _) (by unfold signNorm; positivity)
    _ = D * Real.exp (((N : ℝ) + determinantOrder r d T) * logLength y) := by
      rw [add_mul, Real.exp_add]
      dsimp only [D]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_monotone
      (mul_le_mul_of_nonneg_right hM (logLength_nonneg y))) hD₀

/-- Left equivariance for the continued larger-rank family with the opposite trace character. -/
def HasLeftWhittakerLaw {P : Type} (S : Set P) (a : ℂˣ) (F : P → G' → ℂ) : Prop :=
  ∀ p ∈ S, ∀ u ∈ Langlands.GeneralLinear.upperUnipotent m ℂ, ∀ g : G',
    F p (u * g) = complexWhittakerCharacter (r := r + 1) (-a) u * F p g

private theorem root_character_derivative {P : Type} (S : Set P) (a : ℂˣ) (F : P → G' → ℂ)
    (hF : HasLeftWhittakerLaw S a F) (p : P) (hp : p ∈ S) (y : Y) (i : Fin (r + 1)) (k : K) (J : ℕ) :
    iteratedDeriv J (fun t => F p (logTorus y * rootPath a i t * k.val)) 0 =
      (rootFrequency * (rootRatio y i : ℂ)) ^ J * F p (logTorus y * k.val) := by
  have he (t : ℝ) : F p (logTorus y * rootPath a i t * k.val) =
      Complex.exp ((rootFrequency * (rootRatio y i : ℂ)) * (t : ℂ)) * F p (logTorus y * k.val) := by
    rw [logTorus_mul_rootPath, mul_assoc, hF p hp _ (rootPath_mem _ _ _) _, whittakerCharacter_rootPath,
      Complex.ofReal_mul, mul_assoc]
  simp_rw [he]
  exact iteratedDeriv_exp_linear_zero _ _ _

private theorem uniform_root_bound_of_derivatives {P : Type} (S : Set P) (a : ℂˣ) (F : P → G' → ℂ)
    (hF : HasLeftWhittakerLaw S a F) {N : ℕ}
    (hD : ∀ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S, ∀ (y : Y) (k : K) (i : Fin (r + 1)),
      ‖iteratedDeriv J (fun t => F p (logTorus y * rootPath a i t * k.val)) 0‖ ≤
        C * Real.exp ((N : ℝ) * logLength y)) : HasUniformSimpleRootBound (r := r + 1) S F := by
  obtain ⟨B, hB₀, hB⟩ := hD 0
  refine ⟨N, fun J => ?_⟩
  let M := J * (r + 1)
  obtain ⟨C, hC₀, hC⟩ := hD M
  let A := C / ‖rootFrequency‖ ^ M
  have hω : 0 < ‖rootFrequency‖ := norm_pos_iff.mpr rootFrequency_ne_zero
  have hA : 0 ≤ A := div_nonneg hC₀ (pow_nonneg hω.le _)
  refine ⟨B + A, add_nonneg hB₀ hA, fun p hp g => ?_⟩
  let y := alpha g
  let k := kpart g
  have hg : (npart g).val * (logTorus y * k.val) = g := by
    rw [← mul_assoc, npart_mul_logTorus_mul_kpart]
  have hnorm : ‖F p g‖ = ‖F p (logTorus y * k.val)‖ := by
    rw [← hg, hF p hp _ (npart g).2 _, norm_mul]
    simp only [complexWhittakerCharacter, UnitaryAdditiveCharacter.norm_complex, one_mul]
  rw [hnorm]
  change ‖F p (logTorus y * k.val)‖ ≤ (B + A) * Real.exp ((N : ℝ) * logLength y - (J : ℝ) * rootPos y)
  let δ (i : Fin (r + 1)) := y i.castSucc - y i.succ
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ δ (Finset.univ_nonempty : (Finset.univ : Finset (Fin (r + 1))).Nonempty)
  have hroot : rootPos y ≤ ((r + 1 : ℕ) : ℝ) * max (δ i) 0 := by
    unfold rootPos
    calc
      _ ≤ ∑ _ : Fin (r + 1), max (δ i) 0 := Finset.sum_le_sum fun j _ =>
        max_le_max (hi j (Finset.mem_univ j)) le_rfl
      _ = _ := by simp [nsmul_eq_mul]
  by_cases hpos : 0 ≤ δ i
  · rw [max_eq_left hpos] at hroot
    have he := hC p hp y k i
    rw [root_character_derivative S a F hF p hp y i k M, norm_mul, norm_pow, norm_mul, rootRatio,
      Complex.norm_of_nonneg (Real.exp_pos _).le, mul_pow, ← Real.exp_nat_mul] at he
    have hdiv : ‖F p (logTorus y * k.val)‖ ≤ A * Real.exp ((N : ℝ) * logLength y - (M : ℝ) * δ i) := by
      have hsize : ‖F p (logTorus y * k.val)‖ * (‖rootFrequency‖ ^ M * Real.exp ((M : ℝ) * δ i)) ≤
          C * Real.exp ((N : ℝ) * logLength y) := by
        rw [mul_comm ‖F p (logTorus y * k.val)‖]
        exact he
      have h := (le_div_iff₀ (mul_pos (pow_pos hω M) (Real.exp_pos ((M : ℝ) * δ i)))).2 hsize
      rw [mul_div_mul_comm, ← Real.exp_sub] at h
      exact h
    have hJ : (J : ℝ) * rootPos y ≤ (M : ℝ) * δ i := by
      have hh := mul_le_mul_of_nonneg_left hroot (Nat.cast_nonneg J)
      simpa only [M, Nat.cast_mul, mul_assoc] using hh
    exact hdiv.trans (mul_le_mul (le_add_of_nonneg_left hB₀) (Real.exp_monotone (sub_le_sub_left hJ _))
      (Real.exp_nonneg _) (add_nonneg hB₀ hA))
  · rw [max_eq_right (le_of_not_ge hpos), mul_zero] at hroot
    have hzero : rootPos y = 0 := le_antisymm hroot (rootPos_nonneg _)
    have he := hB p hp y k i
    simp only [iteratedDeriv_zero, rootPath_zero, mul_one] at he
    rw [hzero, mul_zero, sub_zero]
    exact he.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hA) (Real.exp_nonneg _))

variable (r) in
/-- The exact continued Godement family has uniform arbitrary simple-root decay when it
has the left Whittaker law and the smaller family satisfies the uniform hypothesis. -/
def ComplexGodementRootBoundsStatement : Prop :=
  ∀ {P : Type} (ν : Measure G) [ν.IsHaarMeasure] (μ : AdditiveHaarMeasure ℂ)
    (a : ℂˣ) (d : ComplexCharacterData) (S : Set P) (W : P → G → ℂ),
    (∀ p ∈ S, Continuous (W p)) → HasUniformSimpleRootBound S W →
    ∀ (Φ : 𝓢(Rect, ℂ)) (s : P → ℂ) (T : ℝ), 0 ≤ T →
      (∀ p ∈ S, |(addedShift r + s p - 1).re| ≤ T) →
      let F := fun p g => continuedValue ν μ d a Φ (W p) g (s p)
      HasLeftWhittakerLaw S a F → HasUniformSimpleRootBound (r := r + 1) S F

set_option maxHeartbeats 1200000 in
theorem complexGodementRootBounds : ComplexGodementRootBoundsStatement r := by
  intro P ν hν μ a d S W hWc hWb Φ s T hT hs F hLeft
  obtain ⟨N, hN⟩ := exists_root_derivative_bounds ν μ a d S W hWc hWb Φ s T hT hs
  exact uniform_root_bound_of_derivatives S a _ hLeft hN

end Langlands.Global.RankinSelbergGlobal.ComplexGodementRootBounds
