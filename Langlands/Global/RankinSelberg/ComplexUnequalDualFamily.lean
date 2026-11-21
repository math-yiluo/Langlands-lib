import Langlands.Global.RankinSelberg.ComplexUnequalOrdinaryFamily
import Langlands.Global.RankinSelberg.ComplexLocalDualWhittakerGauge
import Langlands.Global.RankinSelberg.ComplexLocalRectangularBounds
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Pi

/-! # Joint holomorphy of the exact dual unequal-rank kernel integral -/

noncomputable section
open MeasureTheory Filter Set
open scoped Classical ENNReal NNReal
open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (inverseTranspose weylLong weylInverseTranspose)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure)
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexUnequalFamily

open ArchimedeanLocal ComplexLocalIwasawa ComplexLocalRectangularBounds
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexLocalOrdinaryConvergence (norm_detPower_logTorus_mul)
open ComplexLocalDualWhittakerGauge (weylLong_mem_unitary inverseTranspose_mem_unitary)
open ComplexLocalWhittakerGauge (logTorus logTorus_val logTorus_inv_val)
open RealConvergenceAnalysis (rootPos rootPos_nonneg)
open RealEqualDualConvergence (revNeg rootPos_revNeg sum_abs_revNeg)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel

private theorem alpha_mul_unitary {n : ℕ} (g : Langlands.GeneralLinear n ℂ)
    (k : unitaryCompact ℂ n) : alpha (g * k.val) = alpha g := by
  conv_lhs => rw [← npart_mul_logTorus_mul_kpart g]
  rw [mul_assoc]
  exact alpha_iwasawa _ _ (kpart g * k)

private theorem alpha_logTorus_mul {n : ℕ} (y : Fin n → ℝ) (k : unitaryCompact ℂ n) :
    alpha (logTorus y * k.val) = y := by
  simpa only [OneMemClass.coe_one, one_mul] using alpha_iwasawa 1 y k

private theorem reindex_mem_unitary {m n : ℕ} (e : m = n) (g : Langlands.GeneralLinear m ℂ)
    (hg : g ∈ unitaryCompact ℂ m) :
    GeneralLinear.reindex (finCongr e) g ∈ unitaryCompact ℂ n := by
  subst n
  rwa [Langlands.RankinSelberg.reindex_finCongr_self]

theorem unfoldingWeyl_mem_unitary {r t : ℕ} (h : t < r) :
    ArchimedeanLocal.unfoldingWeyl (K := ℂ) h ∈ unitaryCompact ℂ (r + 1) := by
  let w := GeneralLinear.weylLong ((r + 1) - (t + 1)) ℂ
  let g : Langlands.GeneralLinear (t + 1) ℂ := 1
  have he : GeneralLinear.blockSum (g, w) =
      Langlands.Archimedean.ComplexBlockParabolic.blockDiagGL g w := by
    apply Units.ext
    rw [Langlands.Archimedean.ComplexBlockLimit.blockDiagGL_val]
    rfl
  have hBlock : GeneralLinear.blockSum (g, w) ∈ unitaryCompact ℂ (t + 1 + ((r + 1) - (t + 1))) := by
    rw [he]
    exact Langlands.Archimedean.ComplexBlockParabolicProof.blockDiagGL_mem_unitaryCompact'
      (one_mem _) (weylLong_mem_unitary _)
  exact reindex_mem_unitary (Nat.add_sub_of_le (Nat.le_of_lt (Nat.succ_lt_succ h))) _ hBlock

private theorem lowerBlockPair_mul_right {m d : ℕ} (g k : Langlands.GeneralLinear m ℂ)
    (x : Matrix (Fin d) (Fin m) ℂ) (b : GeneralLinear.lowerTriangularSubgroup d ℂ) :
    GeneralLinear.lowerBlockPair (g * k) (x * k.val) b =
      GeneralLinear.lowerBlockPair g x b * GeneralLinear.rankInclusion d k := by
  ext i j
  refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i <;>
    refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_add, GeneralLinear.rankInclusion, Matrix.one_apply]

private theorem rectangularPoint_mul_right {r t : ℕ} (h : t < r)
    (g k : Langlands.GeneralLinear (t + 1) ℂ)
    (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ) :
    ArchimedeanLocal.rectangularPoint h (g * k) (x * k.val) =
      ArchimedeanLocal.rectangularPoint h g x * padGL (Nat.succ_le_succ h.le) k := by
  simp only [ArchimedeanLocal.rectangularPoint, GeneralLinear.lowerBlockLocalization,
    lowerBlockPair_mul_right, map_mul]
  rw [Unfolding.reindex_rankInclusion_rankInclusion]

private theorem rectangularPoint_unitary {r t : ℕ} (h : t < r)
    (g : Langlands.GeneralLinear (t + 1) ℂ) (k : unitaryCompact ℂ (t + 1))
    (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ) :
    ArchimedeanLocal.rectangularPoint h (g * k.val) x =
      ArchimedeanLocal.rectangularPoint h g (x * (k.val⁻¹).val) *
        padGL (Nat.succ_le_succ h.le) k.val := by
  rw [← rectangularPoint_mul_right, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

/-! ### The rectangular factor of the majorant -/

private theorem rectangular_sigmaFinite (a : ℂˣ) (d m : ℕ) :
    SigmaFinite (rectangularMeasure (complexSelfDualMeasure a) d m) := by
  let μ := (complexSelfDualMeasure a).measure
  have : μ.IsAddHaarMeasure := (complexSelfDualMeasure a).isAddHaar
  have : SigmaFinite μ := inferInstance
  let : ∀ _ : Fin d, SigmaFinite (Measure.pi (fun _ : Fin m => μ)) :=
    fun _ => Measure.pi.sigmaFinite _
  change SigmaFinite (Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin m => μ)))
  exact Measure.pi.sigmaFinite _

private theorem integrable_exp_logRectangleSize (a : ℂˣ) (d m : ℕ) :
    Integrable (fun x : Matrix (Fin d) (Fin m) ℂ =>
      Real.exp (-(3 * (d : ℝ) * (m : ℝ)) * logRectangleSize x))
      (rectangularMeasure (complexSelfDualMeasure a) d m) := by
  let μ := (complexSelfDualMeasure a).measure
  have : μ.IsAddHaarMeasure := (complexSelfDualMeasure a).isAddHaar
  let f := fun z : ℂ => Real.exp (-3 * Real.log (1 + ‖z‖ ^ 2))
  have hf : Integrable f μ := by
    have h := integrable_rpow_neg_one_add_norm_sq (μ := μ) (E := ℂ) (r := 6)
      (by norm_num [Complex.finrank_real_complex])
    refine h.congr (ae_of_all _ fun z => ?_)
    dsimp only [f]
    rw [Real.rpow_def_of_pos (by positivity)]
    congr 1
    ring
  let F := fun x : Matrix (Fin d) (Fin m) ℂ => ∏ i, ∏ j, f (x i j)
  have hF : Integrable F (rectangularMeasure (complexSelfDualMeasure a) d m) :=
    Integrable.fintype_prod (f := fun (_ : Fin d) (v : Fin m → ℂ) => ∏ j, f (v j))
      (μ := fun _ => Measure.pi (fun _ : Fin m => μ)) fun _ =>
        Integrable.fintype_prod (f := fun _ : Fin m => f) (μ := fun _ => μ) fun _ => hf
  let H := fun x : Matrix (Fin d) (Fin m) ℂ =>
    Real.exp (-(3 * (d : ℝ) * (m : ℝ)) * logRectangleSize x)
  have hHm : Continuous H :=
    Real.continuous_exp.comp (continuous_const.mul continuous_logRectangleSize)
  have hHB (x : Matrix (Fin d) (Fin m) ℂ) : ‖H x‖ ≤ F x := by
    have hx (i : Fin d) (j : Fin m) : Real.log (1 + ‖x i j‖ ^ 2) ≤ logRectangleSize x := by
      apply Real.log_le_log (by positivity)
      apply add_le_add le_rfl
      exact (Finset.single_le_sum (fun q _ => sq_nonneg ‖x i q‖) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (fun p _ => Finset.sum_nonneg fun q _ => sq_nonneg ‖x p q‖)
          (Finset.mem_univ i))
    have hsum : ∑ i, ∑ j, Real.log (1 + ‖x i j‖ ^ 2) ≤
        (d : ℝ) * (m : ℝ) * logRectangleSize x := by
      calc
        _ ≤ ∑ _i : Fin d, ∑ _j : Fin m, logRectangleSize x :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hx i j
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
    rw [Real.norm_of_nonneg (show 0 ≤ H x from Real.exp_nonneg _)]
    dsimp only [H, F, f]
    simp_rw [← Real.exp_sum, ← Finset.mul_sum]
    apply Real.exp_monotone
    calc
      _ = (-3 : ℝ) * ((d : ℝ) * (m : ℝ) * logRectangleSize x) := by ring
      _ ≤ _ := mul_le_mul_of_nonpos_left hsum (by norm_num)
  exact hF.mono' hHm.aestronglyMeasurable (ae_of_all _ hHB)

private theorem inverseTranspose_logTorus {n : ℕ} (y : Fin n → ℝ) :
    inverseTranspose n ℂ (logTorus y) = logTorus (-y) := by
  apply Units.ext
  rw [GeneralLinear.inverseTranspose_coe, logTorus_inv_val, Matrix.diagonal_transpose, logTorus_val]
  rfl

private theorem weylLong_logTorus_weylLong {n : ℕ} (y : Fin n → ℝ) :
    weylLong n ℂ * logTorus y * weylLong n ℂ = logTorus (fun i => y i.rev) := by
  apply Units.ext
  ext i j
  rw [GeneralLinear.weylLong_conjugate_entry]
  simp only [logTorus_val, Matrix.diagonal_apply, Fin.rev_inj]

private def dualUnitary {n : ℕ} (k : unitaryCompact ℂ n) : unitaryCompact ℂ n :=
  ⟨weylLong n ℂ * inverseTranspose n ℂ k.val,
    mul_mem (weylLong_mem_unitary n) (inverseTranspose_mem_unitary k)⟩

private theorem dual_logTorus_mul {r : ℕ}
    (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (y : Fin (r + 1) → ℝ)
    (k : unitaryCompact ℂ (r + 1)) :
    ArchimedeanLocal.dualFunction (r + 1) W (logTorus y * k.val) =
      W (logTorus (revNeg y) * (dualUnitary k).val) := by
  unfold ArchimedeanLocal.dualFunction
  congr 1
  rw [map_mul, inverseTranspose_logTorus]
  have h : logTorus (revNeg y) =
      weylLong (r + 1) ℂ * logTorus (-y) * (weylLong (r + 1) ℂ)⁻¹ := by
    rw [GeneralLinear.weylLong_inv, weylLong_logTorus_weylLong]
    rfl
  rw [h]
  change _ = _ * (weylLong (r + 1) ℂ * inverseTranspose (r + 1) ℂ k.val)
  group

/-- Uniform simple-root bounds transfer to the exact Weyl inverse-transpose family. -/
theorem dual_uniformSimpleRootBound {r : ℕ} {a : ℂˣ} {P : Type*} {S : Set P}
    {W : P → Langlands.GeneralLinear (r + 1) ℂ → ℂ}
    (hW : ∀ p, HasLeftCharacter a (W p)) (hWb : HasUniformSimpleRootBound S W) :
    HasUniformSimpleRootBound S (fun p => ArchimedeanLocal.dualFunction (r + 1) (W p)) := by
  obtain ⟨N, hN⟩ := hWb
  refine ⟨N, fun M => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN M
  refine ⟨C, hC, fun v hv g => ?_⟩
  have h := dual_left_mul (hW v) (npart g) (logTorus (alpha g) * (kpart g).val)
  rw [← mul_assoc, npart_mul_logTorus_mul_kpart] at h
  dsimp only
  rw [h, norm_mul]
  simp only [complexWhittakerCharacter, HarmonicAnalysis.UnitaryAdditiveCharacter.norm_complex,
    one_mul, dual_logTorus_mul]
  have hb' := hb v hv (logTorus (revNeg (alpha g)) * (dualUnitary (kpart g)).val)
  rw [alpha_logTorus_mul, sum_abs_revNeg, rootPos_revNeg] at hb'
  exact hb'

private theorem exponent_bound {m : ℕ} (y : Fin (m + 1) → ℝ) (L : (Fin (m + 1) → ℝ) →L[ℝ] ℝ)
    {A₀ A₁ B T M c X R K : ℝ} (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hc : 0 ≤ c)
    (hX : 0 ≤ X) (hR : 0 ≤ R) (hT : A₀ + A₁ + ‖L‖ + 1 ≤ T)
    (hM : (2 * T + A₀ + c) * K ≤ M)
    (hU : (∑ j, max (y j) 0) + X ≤ K * (1 + R)) :
    A₀ * (B + (∑ j, |y j|) + X) - M * R + A₁ * (∑ j, |y j|) + T * (∑ j, y j) ≤
      A₀ * B + (2 * T + A₀ + c) * K - (∑ j, |y j|) - L y - c * X := by
  let S := ∑ j, |y j|
  let U := ∑ j, max (y j) 0
  let H := 2 * T + A₀ + c
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hU0 : 0 ≤ U := Finset.sum_nonneg fun _ _ => le_max_right _ _
  have hT0 : 0 ≤ T := (by positivity : 0 ≤ A₀ + A₁ + ‖L‖ + 1).trans hT
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have h₁ := congrArg (T * ·) (sum_add_abs y)
  have h₂ := mul_le_mul_of_nonneg_right (show 2 * T ≤ H by dsimp [H]; linarith) hU0
  have h₃ := mul_le_mul_of_nonneg_right (show A₀ + c ≤ H by dsimp [H]; linarith) hX
  change U + X ≤ K * (1 + R) at hU
  have h₄ := mul_le_mul_of_nonneg_left hU hH
  have h₅ := mul_le_mul_of_nonneg_right hM hR
  have h₆ := mul_le_mul_of_nonneg_right hT hS
  have h₇ := RealEqualConvergence.linear_le L y
  change L y ≤ ‖L‖ * S at h₇
  change A₀ * (B + S + X) - M * R + A₁ * S + T * (∑ j, y j) ≤ A₀ * B + H * K - S - L y - c * X
  nlinarith only [h₁, h₂, h₃, h₄, h₅, h₆, h₇]

section Dual

variable {r t : ℕ} (h : t < r) (a : ℂˣ)
local notation "GT" => Langlands.GeneralLinear (t + 1) ℂ
local notation "GR" => Langlands.GeneralLinear (r + 1) ℂ
local notation "Rect" => Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ

/-- Uniform simple-root bounds give an integrable product majorant for the dual kernel on
bounded real spectral intervals above a fixed threshold. -/
theorem dual_halfPlaneDomination {P : Type*} (D : ComplexQuotientMeasureData t)
    (S : Set P) (W : P → GR → ℂ) (V : P → GT → ℂ) (s : P → ℂ)
    (hW : ∀ p, HasLeftCharacter a (W p)) (hV : ∀ p, HasLeftCharacter (-a) (V p))
    (hWb : HasUniformSimpleRootBound S W) (hVb : HasUniformSimpleRootBound S V) :
    ∃ σ, HalfPlaneDomination (complexUnequalDualMeasure (r := r) a D) S s
      (fun p => complexUnequalDualKernel h (W p) (V p) (s p)) σ := by
  obtain ⟨κ, L, hκL⟩ := complexIwasawaToralMeasure t D
  obtain ⟨B, K, _, hK, hBK⟩ := complexLocalRectangularBounds h
  obtain ⟨N, hN⟩ := dual_uniformSimpleRootBound hW hWb
  obtain ⟨N', hN'⟩ := dual_uniformSimpleRootBound hV hVb
  obtain ⟨C₂, hC₂, hb₂⟩ := hN' 0
  let A₀ : ℝ := (N : ℝ) * ((r + 1 : ℕ) : ℝ)
  let A₁ : ℝ := N'
  let gap : ℝ := ((r - t : ℕ) : ℝ)
  let c : ℝ := 3 * (((r - (t + 1) : ℕ) : ℝ)) * (((t + 1 : ℕ) : ℝ))
  let σ : ℝ := (A₀ + A₁ + ‖L‖ + 1 + gap) / 2
  have hA₀ : 0 ≤ A₀ := by dsimp [A₀]; positivity
  have hA₁ : 0 ≤ A₁ := Nat.cast_nonneg _
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨σ, fun τ => ?_⟩
  let J := (2 * (2 * τ - gap) + A₀ + c) * K
  obtain ⟨M, hM⟩ := exists_nat_gt J
  obtain ⟨C₁, hC₁, hb₁⟩ := hN M
  let C := C₁ * C₂ * Real.exp (A₀ * B + J)
  let μ := rectangularMeasure (complexSelfDualMeasure a) (r - (t + 1)) (t + 1)
  have : SigmaFinite μ := rectangular_sigmaFinite a _ _
  have hr : Integrable (fun x : Rect => Real.exp (-c * logRectangleSize x)) μ :=
    integrable_exp_logRectangleSize a _ _
  refine ⟨fun z => C * (Real.exp (-(∑ j, |alphaQ z.1 j|) - L (alphaQ z.1)) *
    Real.exp (-c * logRectangleSize z.2)),
    ((integrable_toralMajorant D κ L hκL).mul_prod hr).const_mul C, fun v hv hvσ hvτ z => ?_⟩
  let T : ℝ := 2 * (s v).re - gap
  have hT : A₀ + A₁ + ‖L‖ + 1 ≤ T := by dsimp [T, σ] at *; linarith
  have hJT : (2 * T + A₀ + c) * K ≤ J :=
    mul_le_mul_of_nonneg_right (by dsimp [T]; linarith) hK
  have hgap : 2 * (s v - ((r - t : ℕ) : ℂ) / 2).re = T := by
    rw [show ((r - t : ℕ) : ℂ) / 2 = ((gap / 2 : ℝ) : ℂ) by push_cast [gap]; rfl,
      Complex.sub_re, Complex.ofReal_re]
    dsimp [T]
    ring
  have hrep (y : Fin (t + 1) → ℝ) (k : unitaryCompact ℂ (t + 1)) (x : Rect) :
      ‖complexUnequalDualKernel h (W v) (V v) (s v)
          (Quotient.mk _ (logTorus y * (k : GT)), x)‖ ≤
        C * (Real.exp (-(∑ j, |y j|) - L y) * Real.exp (-c * logRectangleSize x)) := by
    let g := logTorus y * (k : GT)
    let X := logRectangleSize x
    let len := ∑ j, |y j|
    let x' := x * ((k : GT)⁻¹).val
    let P := ArchimedeanLocal.rectangularPoint h (logTorus y) x'
    let R := rootPos (alpha P)
    let p := Nat.succ_le_succ h.le
    let k' : unitaryCompact ℂ (r + 1) :=
      ⟨padGL p (k : GT) * ArchimedeanLocal.unfoldingWeyl h,
        mul_mem (unitary_padGL p (k : GT) k.2) (unfoldingWeyl_mem_unitary h)⟩
    have hg : ArchimedeanLocal.rectangularPoint h g x * ArchimedeanLocal.unfoldingWeyl h =
        P * (k' : GR) := by
      rw [rectangularPoint_unitary h (logTorus y) k, mul_assoc]
    have hX : logRectangleSize x' = X := logRectangleSize_mul_unitary x k⁻¹
    obtain ⟨hlen, hU⟩ := hBK y x'
    rw [hX] at hlen hU
    have h₁' := hb₁ v hv (P * (k' : GR))
    rw [alpha_mul_unitary P k'] at h₁'
    have h₁ : ‖ArchimedeanLocal.dualFunction (r + 1) (W v) (P * (k' : GR))‖ ≤
        C₁ * Real.exp (A₀ * (B + len + X) - (M : ℝ) * R) := by
      refine h₁'.trans (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) hC₁)
      have hlen' := mul_le_mul_of_nonneg_left hlen (Nat.cast_nonneg (α := ℝ) N)
      exact sub_le_sub_right (by simpa only [A₀, mul_assoc] using hlen') _
    have h₂ : ‖ArchimedeanLocal.dualFunction (t + 1) (V v) g‖ ≤ C₂ * Real.exp (A₁ * len) := by
      have hv' := hb₂ v hv (logTorus y * (k : GT))
      rw [alpha_logTorus_mul y k] at hv'
      simpa only [Nat.cast_zero, zero_mul, sub_zero] using hv'
    rw [dualKernel_mk h (hW v) (hV v), hg, norm_mul, norm_mul,
      norm_detPower_logTorus_mul, hgap]
    have hE : A₀ * (B + len + X) - (M : ℝ) * R + A₁ * len + T * (∑ j, y j) ≤
        A₀ * B + J - len - L y - c * X := by
      have hET := exponent_bound y L (B := B) hA₀ hA₁ hc (logRectangleSize_nonneg x) (rootPos_nonneg _)
        hT (hJT.trans hM.le) hU
      dsimp only [len, X, R] at *
      exact hET.trans (by linarith)
    calc
      _ ≤ (C₁ * Real.exp (A₀ * (B + len + X) - (M : ℝ) * R)) *
          (C₂ * Real.exp (A₁ * len)) * Real.exp (T * ∑ j, y j) :=
        mul_le_mul_of_nonneg_right (mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity))
          (Real.exp_nonneg _)
      _ = C₁ * C₂ * Real.exp (A₀ * (B + len + X) - (M : ℝ) * R + A₁ * len + T * (∑ j, y j)) := by
        rw [Real.exp_add, Real.exp_add]
        ring
      _ ≤ C₁ * C₂ * Real.exp (A₀ * B + J - len - L y - c * X) :=
        mul_le_mul_of_nonneg_left (Real.exp_monotone hE) (mul_nonneg hC₁ hC₂)
      _ = C * (Real.exp (-len - L y) * Real.exp (-c * X)) := by
        have he : A₀ * B + J - len - L y - c * X = (A₀ * B + J) + (-len - L y) + (-c * X) := by ring
        rw [he, Real.exp_add, Real.exp_add]
        dsimp only [C]
        ring
  obtain ⟨q, x⟩ := z
  induction q using Quotient.inductionOn with
  | h g =>
    dsimp only
    rw [alphaQ_mk, mk_eq_mk_logTorus_mul_kpart g]
    exact hrep (alpha g) (kpart g) x

/-- On absolute convergence, the exact iterated dual integral is the product integral. -/
theorem dualIntegral_eq_prod (D : ComplexQuotientMeasureData t)
    (W : GR → ℂ) (V : GT → ℂ) (s : ℂ)
    (hint : Integrable (complexUnequalDualKernel h W V s) (complexUnequalDualMeasure (r := r) a D)) :
    complexUnequalDualIntegral h a D W V s =
      ∫ z, complexUnequalDualKernel h W V s z ∂complexUnequalDualMeasure (r := r) a D := by
  have : SecondCountableTopology (Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin (t + 1) → Fin (t + 1) → ℂ))
  have : SecondCountableTopology (Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  have : SecondCountableTopology GT := Units.isInducing_embedProduct.secondCountableTopology
  have : LocallyCompactSpace (Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin (t + 1) → Fin (t + 1) → ℂ))
  have : SigmaCompactSpace (LeftUnipotentQuotient t ℂ) := by
    have hq := QuotientIntegration.leftQuotient_isOpenQuotientMap
      (GeneralLinear.upperUnipotent (t + 1) ℂ)
    apply isSigmaCompact_univ_iff.mp
    rw [← Set.range_eq_univ.mpr hq.surjective]
    exact isSigmaCompact_range hq.continuous
  have : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  have : D.measure.Regular := D.compatible.regular
  have : SigmaFinite (rectangularMeasure (complexSelfDualMeasure a) (r - (t + 1)) (t + 1)) :=
    rectangular_sigmaFinite a _ _
  exact (integral_prod _ hint).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Holomorphy and integrability of the exact dual unequal-rank integral, jointly in a
finite-dimensional complex parameter space. -/
def ComplexUnequalDualFamilyStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData t) (S : Set E) (W : E → GR → ℂ) (V : E → GT → ℂ)
    (s : E → ℂ), IsOpen S → Differentiable ℂ s →
    (∀ p, HasLeftCharacter a (W p)) → (∀ p, HasLeftCharacter (-a) (V p)) →
    (∀ p, Continuous (W p)) → (∀ p, Continuous (V p)) →
    (∀ g, DifferentiableOn ℂ (W · g) S) → (∀ g, DifferentiableOn ℂ (V · g) S) →
    HasUniformSimpleRootBound S W → HasUniformSimpleRootBound S V →
    ∃ σ : ℝ,
      (∀ p ∈ S ∩ {v | σ < (s v).re}, Integrable (complexUnequalDualKernel h (W p) (V p) (s p))
        (complexUnequalDualMeasure (r := r) a D)) ∧
      DifferentiableOn ℂ (fun p => complexUnequalDualIntegral h a D (W p) (V p) (s p))
        (S ∩ {v | σ < (s v).re})

theorem complexUnequalDualFamily : ComplexUnequalDualFamilyStatement (E := E) h a := by
  intro D S W V s hS hs hW hV hWc hVc hWd hVd hWb hVb
  obtain ⟨σ, hdom⟩ := dual_halfPlaneDomination h a D S W V s hW hV hWb hVb
  have hD (z : LeftUnipotentQuotient t ℂ × Rect) :
      DifferentiableOn ℂ (fun p => complexUnequalDualKernel h (W p) (V p) (s p) z) S := by
    let g := z.1.out
    let g₁ := weylInverseTranspose (r + 1) ℂ
      (ArchimedeanLocal.rectangularPoint h g z.2 * ArchimedeanLocal.unfoldingWeyl h)
    let g₂ := weylInverseTranspose (t + 1) ℂ g
    change DifferentiableOn ℂ (fun p => W p g₁ * V p g₂ *
      ArchimedeanLocal.detPower complexNormalizedAbs g (s p - ((r - t : ℕ) : ℂ) / 2)) S
    exact ((hWd _).mul (hVd _)).mul (differentiable_detPower_parameter g hs _).differentiableOn
  obtain ⟨hint, hdiff⟩ := differentiableOn_integral_of_halfPlaneDomination hS hs (fun p =>
    (continuous_dualKernel h (hW p) (hV p) (hWc p) (hVc p) (s p)).aestronglyMeasurable) hD hdom
  exact ⟨σ, hint, hdiff.congr fun p hp => dualIntegral_eq_prod h a D (W p) (V p) (s p) (hint p hp)⟩

end Dual

end Langlands.Global.RankinSelbergGlobal.ComplexUnequalFamily
