import Langlands.Representation.Archimedean.ComplexGLTwoJacquetOrderingReduction
import Langlands.Representation.Archimedean.ComplexSwapJacquetProof
import Langlands.Representation.Archimedean.ComplexGLTwoMomentAnalysis

/-!
# The moments of the `GL_2(ℂ)` principal series

Proof of `ComplexGLTwoMomentJacquetStatement` (`complexGLTwoMomentJacquet`). Since
`w n(z)` is the chart `s x(z)` of `ComplexSwapJacquet` at positions `0, 1`, the moment
`M_{i,j} f` is `∫ φ(z) z^i z̄^j` with `φ(z) = f(s x(z))`. The chart formulas
(`chartLieFacts`) express the right derivatives of `f` along the chart through `φ` and
`Dφ`, the decay `|g(s x(z))| ≤ C (1 + |z|)^(-(2 + 2 Re(t_0 - t_1)))` holds for every `g`
of the standard module, and the weighted integration-by-parts identities of
`ComplexGLTwoMomentAnalysis` give the formulas.
-/

noncomputable section

open scoped TensorProduct Matrix

open MeasureTheory Filter Topology

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

namespace ComplexGLTwoMoment

open ComplexSwapJacquet

/-! ## Decay along the chart -/

theorem rpow_neg_le_two_rpow_mul {x r : ℝ} (hx : 1 ≤ x) (hr : 0 ≤ r) :
    x ^ (-r) ≤ 2 ^ r * (1 + x) ^ (-r) := by
  have h1 : (2 * x) ^ (-r) ≤ (1 + x) ^ (-r) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  rw [Real.mul_rpow (by norm_num) (by linarith)] at h1
  have h2 : (2 : ℝ) ^ r * 2 ^ (-r) = 1 := by
    rw [Real.rpow_neg (by norm_num), mul_inv_cancel₀ (by positivity)]
  calc x ^ (-r) = 2 ^ r * (2 ^ (-r) * x ^ (-r)) := by rw [← mul_assoc, h2, one_mul]
    _ ≤ 2 ^ r * (1 + x) ^ (-r) := mul_le_mul_of_nonneg_left h1 (by positivity)

theorem one_le_two_rpow_mul {x r : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) (hr : 0 ≤ r) :
    1 ≤ 2 ^ r * (1 + x) ^ (-r) := by
  have h1 : (2 : ℝ) ^ (-r) ≤ (1 + x) ^ (-r) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have h2 : (2 : ℝ) ^ r * 2 ^ (-r) = 1 := by
    rw [Real.rpow_neg (by norm_num), mul_inv_cancel₀ (by positivity)]
  calc (1 : ℝ) = 2 ^ r * 2 ^ (-r) := h2.symm
    _ ≤ 2 ^ r * (1 + x) ^ (-r) := mul_le_mul_of_nonneg_left h1 (by positivity)

variable {n : ℕ}

/-- **Decay.** `|h(chart z)| ≤ C (1 + |z|)^(-2 - 2 Re(t_d - t_e))` when
`Re(t_d - t_e) ≥ 0`. -/
theorem exists_bound_chart_rpow (pre post : List ComplexCharacterData)
    (d e : ComplexCharacterData) (i j : Fin n) (hi : (i : ℕ) = pre.length)
    (hj : (j : ℕ) = i + 1) (hre : 0 ≤ (d.exponent - e.exponent).re)
    {h : Langlands.GeneralLinear n ℂ → ℂ}
    (hh : h ∈ complexStandardModule n (pre ++ d :: e :: post)) :
    ∃ C, ∀ z, ‖h (ComplexSwapJacquet.chart i j hj z)‖ ≤
      C * (1 + ‖z‖) ^ (-(2 + 2 * (d.exponent - e.exponent).re)) := by
  set r := 2 + 2 * (d.exponent - e.exponent).re with hr_def
  have hr : 0 ≤ r := by linarith
  obtain ⟨M, hM0, hM⟩ := exists_bound_ball (contDiff_apply_lowerChart hh.1 i j hj).continuous
  obtain ⟨M', hM'0, hM'⟩ := exists_bound_ball (contDiff_apply_chart hh.1 i j hj).continuous
  refine ⟨2 ^ r * (M + M'), fun z => ?_⟩
  have hp : 0 ≤ (1 + ‖z‖) ^ (-r) := by positivity
  rcases le_total ‖z‖ 1 with hz | hz
  · have h1 := one_le_two_rpow_mul (norm_nonneg z) hz hr
    calc ‖h (ComplexSwapJacquet.chart i j hj z)‖ ≤ M' := hM' z hz
      _ ≤ (M + M') * (2 ^ r * (1 + ‖z‖) ^ (-r)) := by nlinarith
      _ = 2 ^ r * (M + M') * (1 + ‖z‖) ^ (-r) := by ring
  · have hz0 : z ≠ 0 := by
      rintro rfl
      simp at hz
      linarith
    have hw : ‖z⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hz
    have hchar := norm_principalSeriesCharacter_chartTorus pre post d e i j hi hj
      (Units.mk0 z hz0)
    rw [Units.val_mk0] at hchar
    have heq : ‖z‖ ^ (-2 - 2 * (d.exponent - e.exponent).re) = ‖z‖ ^ (-r) := by
      rw [hr_def]
      ring_nf
    have h2 := rpow_neg_le_two_rpow_mul hz hr
    have h3 := hM z⁻¹ hw
    rw [apply_chart_eq hh i j hj z hz0, norm_mul, hchar, heq]
    calc ‖z‖ ^ (-r) * ‖h (lowerChart i j hj z⁻¹)‖
        ≤ (2 ^ r * (1 + ‖z‖) ^ (-r)) * (M + M') :=
          mul_le_mul h2 (by linarith) (norm_nonneg _) (by positivity)
      _ = 2 ^ r * (M + M') * (1 + ‖z‖) ^ (-r) := by ring

/-! ## The chart for `n = 2` -/

theorem hj01 : ((1 : Fin 2) : ℕ) = ((0 : Fin 2) : ℕ) + 1 := rfl

theorem weyl_mul_unipotent (z : ℂ) :
    complexGLTwoWeyl * complexGLTwoUnipotent z =
      ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z := by
  apply Units.ext
  rw [Units.val_mul, chart_val]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [complexGLTwoWeyl, complexGLTwoUnipotent, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.swap, Matrix.transvection, Matrix.one_apply,
      Matrix.single_apply]

theorem ofFn_eq (d : Fin 2 → ComplexCharacterData) :
    List.ofFn d = [] ++ d 0 :: d 1 :: [] := by
  simp [List.ofFn_succ]

theorem kappa_ofFn_one (d : Fin 2 → ComplexCharacterData) (k : Fin 2) :
    kappa (List.ofFn d) (List.length_ofFn) k 1 =
      2 * (d k).exponent + 1 - 2 * ((k : ℕ) : ℂ) := by
  rw [kappa_one]
  fin_cases k <;> simp <;> ring

theorem kappa_ofFn_I (d : Fin 2 → ComplexCharacterData) (k : Fin 2) :
    kappa (List.ofFn d) (List.length_ofFn) k Complex.I =
      Complex.I * ((d k).weight : ℂ) := by
  rw [kappa_I]
  fin_cases k <;> simp

/-! ## Bounds along the chart -/

/-- The moment as an integral along the chart `s x(z) = w n(z)`. -/
theorem moment_eq (i j : ℕ) (g : Langlands.GeneralLinear 2 ℂ → ℂ) :
    complexGLTwoMoment i j g =
      ∫ z, g (ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z) * weight i j z := by
  unfold complexGLTwoMoment
  congr 1
  funext z
  rw [weyl_mul_unipotent, weight, mul_assoc]

theorem exists_bound_module (d : Fin 2 → ComplexCharacterData)
    (hre : 0 ≤ ((d 0).exponent - (d 1).exponent).re)
    {g : Langlands.GeneralLinear 2 ℂ → ℂ} (hg : g ∈ complexStandardModule 2 (List.ofFn d)) :
    ∃ C, ∀ z, ‖g (ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z)‖ ≤
      C * (1 + ‖z‖) ^ (-(2 + 2 * ((d 0).exponent - (d 1).exponent).re)) := by
  rw [ofFn_eq d] at hg
  exact exists_bound_chart_rpow [] [] (d 0) (d 1) (0 : Fin 2) 1 rfl hj01 hre hg

theorem bound_mono {x C C' p : ℝ} (h : x ≤ C * p) (hC : C ≤ C') (hp : 0 ≤ p) :
    x ≤ C' * p :=
  h.trans (mul_le_mul_of_nonneg_right hC hp)

/-- The five bounds needed by the weighted integration-by-parts lemmas, with a common
constant: `φ(z) = f(s x(z))` and `Dφ(z)(1)`, `Dφ(z)(i)`, `Dφ(z)(z)`, `Dφ(z)(i z)` are all
`O((1 + |z|)^(-(2 + 2 Re(t_0 - t_1))))`. -/
theorem exists_bounds (d : Fin 2 → ComplexCharacterData)
    (hre : 0 ≤ ((d 0).exponent - (d 1).exponent).re)
    {f : Langlands.GeneralLinear 2 ℂ → ℂ} (hf : f ∈ complexStandardModule 2 (List.ofFn d)) :
    ∃ C, (∀ z, ‖f (ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z)‖ ≤
        C * (1 + ‖z‖) ^ (-(2 + 2 * ((d 0).exponent - (d 1).exponent).re))) ∧
      (∀ z, ‖fderiv ℝ (fun z => f (ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z)) z 1‖ ≤
        C * (1 + ‖z‖) ^ (-(2 + 2 * ((d 0).exponent - (d 1).exponent).re))) ∧
      (∀ z, ‖fderiv ℝ (fun z => f (ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z)) z
          Complex.I‖ ≤
        C * (1 + ‖z‖) ^ (-(2 + 2 * ((d 0).exponent - (d 1).exponent).re))) ∧
      (∀ z, ‖fderiv ℝ (fun z => f (ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z)) z z‖ ≤
        C * (1 + ‖z‖) ^ (-(2 + 2 * ((d 0).exponent - (d 1).exponent).re))) ∧
      (∀ z, ‖fderiv ℝ (fun z => f (ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z)) z
          (Complex.I * z)‖ ≤
        C * (1 + ‖z‖) ^ (-(2 + 2 * ((d 0).exponent - (d 1).exponent).re))) := by
  set a := 2 + 2 * ((d 0).exponent - (d 1).exponent).re with ha
  have LF := chartLieFacts (List.ofFn d) List.length_ofFn (0 : Fin 2) 1 hj01
  have hsingle : ∀ w : ℂ, ∃ C, ∀ z,
      ‖fderiv ℝ (fun z => f (ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z)) z w‖ ≤
        C * (1 + ‖z‖) ^ (-a) := by
    intro w
    obtain ⟨C, hC⟩ := exists_bound_module d hre
      (rightDerivative_mem_principalSeries _ hf (Matrix.single (0 : Fin 2) 1 w))
    exact ⟨C, fun z => by rw [← LF.single_ij f hf w z]; exact hC z⟩
  have hdiag : ∀ c : ℂ, ∃ C, ∀ z,
      ‖fderiv ℝ (fun z => f (ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z)) z (c * z)‖ ≤
        C * (1 + ‖z‖) ^ (-a) := by
    intro c
    set g : Langlands.GeneralLinear 2 ℂ → ℂ :=
      rightDerivative (matrixModel ℂ 2) (Matrix.single (1 : Fin 2) 1 c) f -
        kappa (List.ofFn d) List.length_ofFn 0 c • f with hg_def
    have hg : g ∈ complexStandardModule 2 (List.ofFn d) :=
      Submodule.sub_mem _ (rightDerivative_mem_principalSeries _ hf _)
        (Submodule.smul_mem _ _ hf)
    obtain ⟨C, hC⟩ := exists_bound_module d hre hg
    refine ⟨C, fun z => ?_⟩
    have hz : g (ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z) =
        fderiv ℝ (fun z => f (ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z)) z (c * z) := by
      simp only [hg_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, LF.diag_j f hf c z]
      ring
    rw [← hz]
    exact hC z
  obtain ⟨C₀, h₀⟩ := exists_bound_module d hre hf
  obtain ⟨C₁, h₁⟩ := hsingle 1
  obtain ⟨C₂, h₂⟩ := hsingle Complex.I
  obtain ⟨C₃, h₃⟩ := hdiag 1
  obtain ⟨C₄, h₄⟩ := hdiag Complex.I
  refine ⟨max C₀ (max C₁ (max C₂ (max C₃ C₄))),
    fun z => bound_mono (h₀ z) (by simp) (by positivity),
    fun z => bound_mono (h₁ z) (by simp) (by positivity),
    fun z => bound_mono (h₂ z) (by simp) (by positivity),
    fun z => bound_mono (by simpa only [one_mul] using h₃ z) (by simp) (by positivity),
    fun z => bound_mono (h₄ z) (by simp) (by positivity)⟩

/-- Splitting a weighted integral of `ψ = κ φ + s D`. -/
theorem integral_mul_weight_eq {φ ψ D : ℂ → ℂ} (κ s : ℂ) (i j : ℕ)
    (hpt : ∀ z, ψ z = κ * φ z + s * D z) (hφ : Integrable fun z => φ z * weight i j z)
    (hD : Integrable fun z => D z * weight i j z) :
    ∫ z, ψ z * weight i j z =
      κ * (∫ z, φ z * weight i j z) + s * ∫ z, D z * weight i j z := by
  have h : ∀ z, ψ z * weight i j z = κ * (φ z * weight i j z) + s * (D z * weight i j z) := by
    intro z
    rw [hpt]
    ring
  simp only [h]
  rw [integral_add (hφ.const_mul κ) (hD.const_mul s), integral_const_mul, integral_const_mul]

end ComplexGLTwoMoment

/-! ## The moment statement -/

open ComplexSwapJacquet ComplexGLTwoMoment in
/-- Proof of `ComplexGLTwoMomentJacquetStatement`. -/
theorem complexGLTwoMomentJacquet : ComplexGLTwoMomentJacquetStatement := by
  intro d i j hij f hf
  have hf' : f ∈ complexStandardModule 2 (List.ofFn d) := mem_of_mem_kFs hf
  have hre : 0 ≤ ((d 0).exponent - (d 1).exponent).re := by
    rw [Complex.sub_re]
    have : (0 : ℝ) ≤ ((i + j : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have ha : ((i + j : ℕ) : ℝ) + 2 < 2 + 2 * ((d 0).exponent - (d 1).exponent).re := by
    rw [Complex.sub_re]
    linarith
  obtain ⟨C, hb, h1, hI, hz, hIz⟩ := exists_bounds d hre hf'
  have LF := chartLieFacts (List.ofFn d) List.length_ofFn (0 : Fin 2) 1 hj01
  have hφ : ContDiff ℝ 1 fun z => f (ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z) :=
    contDiff_one_chart hf'
  have hP := integrable_mul_weight i j hφ.continuous ha hb (le_refl (i + j))
  have hDz : Integrable fun z =>
      fderiv ℝ (fun z => f (ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z)) z z *
        weight i j z :=
    integrable_fderiv_apply_mul_weight i j hφ ha continuous_id hz
  have hDIz : Integrable fun z =>
      fderiv ℝ (fun z => f (ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z)) z
          (Complex.I * z) * weight i j z :=
    integrable_fderiv_apply_mul_weight i j hφ ha (continuous_const.mul continuous_id) hIz
  have eM := moment_eq i j f
  refine ⟨?_, ?_, ?_⟩
  · refine hP.congr (Eventually.of_forall fun z => ?_)
    simp only [weight, weyl_mul_unipotent, mul_assoc]
  · intro X hX
    have hX' : ∀ a b : Fin 2, b ≤ a → X a b = 0 := fun a b h => hX a b h
    have hpt : ∀ z, rightDerivative (matrixModel ℂ 2) X f
        (ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z) =
        fderiv ℝ (fun z => f (ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z)) z (X 0 1) := by
      intro z
      have hadd := ComplexSwapJacquet.rightDerivative_add (X - Matrix.single 0 1 (X 0 1))
        (Matrix.single 0 1 (X 0 1)) f (ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z)
      rw [sub_add_cancel] at hadd
      rw [hadd, LF.strictUpper f hf' _ (strictUpper_sub_single hj01 hX') (by simp), zero_add,
        LF.single_ij f hf']
    simp only [moment_eq, hpt]
    exact integral_fderiv_mul_weight i j hφ ha hb h1 hI (X 0 1)
  · rw [Fin.forall_fin_two]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · have e := integral_mul_weight_eq (ψ := fun z => rightDerivative (matrixModel ℂ 2)
        (Matrix.single 0 0 1) f (ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z))
        (kappa (List.ofFn d) List.length_ofFn 1 1) (-1) i j
        (fun z => by rw [LF.diag_i f hf' 1 z, one_mul]; ring) hP hDz
      rw [moment_eq, e, ← eM, integral_fderiv_self_mul_weight i j hφ ha hb hz, ← eM,
        kappa_ofFn_one]
      simp only [Matrix.cons_val_zero, Fin.val_one, Nat.cast_one]
      push_cast
      ring
    · have e := integral_mul_weight_eq (ψ := fun z => rightDerivative (matrixModel ℂ 2)
        (Matrix.single 0 0 Complex.I) f (ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z))
        (kappa (List.ofFn d) List.length_ofFn 1 Complex.I) (-1) i j (fun z => by rw [LF.diag_i f hf' Complex.I z]; ring) hP hDIz
      rw [moment_eq, e, ← eM, integral_fderiv_I_mul_self_mul_weight i j hφ ha hb hIz, ← eM,
        kappa_ofFn_I]
      simp only [Matrix.cons_val_zero]
      ring
    · have e := integral_mul_weight_eq (ψ := fun z => rightDerivative (matrixModel ℂ 2)
        (Matrix.single 1 1 1) f (ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z))
        (kappa (List.ofFn d) List.length_ofFn 0 1) 1 i j
        (fun z => by rw [LF.diag_j f hf' 1 z, one_mul]; ring) hP hDz
      rw [moment_eq, e, ← eM, integral_fderiv_self_mul_weight i j hφ ha hb hz, ← eM,
        kappa_ofFn_one]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Fin.val_zero, Nat.cast_zero]
      push_cast
      ring
    · have e := integral_mul_weight_eq (ψ := fun z => rightDerivative (matrixModel ℂ 2)
        (Matrix.single 1 1 Complex.I) f (ComplexSwapJacquet.chart (0 : Fin 2) 1 hj01 z))
        (kappa (List.ofFn d) List.length_ofFn 0 Complex.I) 1 i j (fun z => by rw [LF.diag_j f hf' Complex.I z]; ring) hP hDIz
      rw [moment_eq, e, ← eM, integral_fderiv_I_mul_self_mul_weight i j hφ ha hb hIz, ← eM,
        kappa_ofFn_I]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      ring

end Langlands.Archimedean
