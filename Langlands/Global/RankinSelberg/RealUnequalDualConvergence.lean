import Langlands.Global.RankinSelberg.RealUnequalConvergence
import Langlands.Global.RankinSelberg.RealRectangularIwasawa
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Pi

/-! # Convergence and holomorphy of the real unequal-rank dual block integral -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealUnequalDualConvergence

open Langlands.Archimedean (unitaryCompact)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure)
open Langlands.QuotientIntegration (descend)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open ArchimedeanLocal RealIwasawa RealConvergenceAnalysis RealEqualConvergence
  RealRectangularIwasawa

local instance realUDualGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
local instance realUDualGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
local instance realUDualNMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
local instance realUDualNBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
local instance realUDualQMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
local instance realUDualQBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩
local instance realUDualMatSC (d a : ℕ) : SecondCountableTopology (Matrix (Fin d) (Fin a) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin d → Fin a → ℝ))

variable {r t : ℕ}

/-! ### The gauge at an arbitrary point -/

theorem kpart_unipotent_mul {n : ℕ} (u : Langlands.GeneralLinear.upperUnipotent n ℝ)
    (g : Langlands.GeneralLinear n ℝ) :
    kpart ((u : Langlands.GeneralLinear n ℝ) * g) = kpart g := by
  conv_lhs => rw [← npart_mul_torus_mul_kpart g]
  rw [← mul_assoc, ← mul_assoc]
  exact kpart_iwasawa (u * npart g) (alpha g) (kpart g)

/-- If `‖V‖` is left invariant under the upper unipotent group, the gauge estimate holds at every
point, in the toral Iwasawa coordinate. -/
theorem gauge_any {n : ℕ} {V : Langlands.GeneralLinear (n + 1) ℝ → ℂ}
    (hVabs : ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ, ∀ g, ‖V (u * g)‖ = ‖V g‖)
    (hV : HasGauge V) :
    ∃ N : ℕ, ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖V g‖ ≤ C * Real.exp (-(M : ℝ) * rootPos (alpha g) + (N : ℝ) * ∑ j, |alpha g j|) := by
  obtain ⟨N, hN⟩ := hV
  refine ⟨N, fun M => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN M
  refine ⟨C, hC, fun g => ?_⟩
  calc
    ‖V g‖ = ‖V ((npart g : Langlands.GeneralLinear (n + 1) ℝ) *
        (torus (alpha g) * (kpart g : Langlands.GeneralLinear (n + 1) ℝ)))‖ := by
      rw [← mul_assoc, npart_mul_torus_mul_kpart]
    _ = ‖V (torus (alpha g) * (kpart g : Langlands.GeneralLinear (n + 1) ℝ))‖ :=
      hVabs _ (npart g).2 _
    _ ≤ _ := hb (alpha g) (kpart g)

theorem rootPos_cast {N N' : ℕ} (e : N + 1 = N' + 1) (z : Fin (N + 1) → ℝ) :
    rootPos (fun i : Fin (N' + 1) => z (Fin.cast e.symm i)) = rootPos z := by
  obtain rfl : N = N' := by omega
  rfl

theorem sum_abs_cast {N N' : ℕ} (e : N + 1 = N' + 1) (z : Fin (N + 1) → ℝ) :
    ∑ i : Fin (N' + 1), |z (Fin.cast e.symm i)| = ∑ i, |z i| := by
  obtain rfl : N = N' := by omega
  rfl

/-- The size identity behind `rectangularPoint`. -/
theorem rect_size (h : t < r) : t + 1 + (r - (t + 1)) + 1 = r + 1 :=
  congrArg (fun a : ℕ => a + 1) (Nat.add_sub_of_le (Nat.succ_le_of_lt h))

theorem rectangularPoint_eq (h : t < r) (g : Langlands.GeneralLinear (t + 1) ℝ)
    (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ) :
    rectangularPoint h g x = GeneralLinear.reindex (finCongr (rect_size h)) (rect g x) := rfl

/-- **The gauge estimate at the rectangular point.** -/
theorem rect_bound (h : t < r) {V : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hVabs : ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g, ‖V (u * g)‖ = ‖V g‖)
    (hV : HasGauge V) :
    ∃ N : ℕ, ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : Fin (t + 1) → ℝ) (k : unitaryCompact ℝ (t + 1))
      (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ),
      ‖V (rectangularPoint h (torus y * (k : Langlands.GeneralLinear (t + 1) ℝ)) x)‖ ≤
        C * Real.exp (-(M : ℝ) * (∑ j, max (y j) 0 +
            ((t : ℝ) + 1) * Real.log (1 + frob x) / 2) +
          (N : ℝ) * (∑ j, |y j| +
            (((t : ℝ) + 1) + ((r - (t + 1) : ℕ) : ℝ)) * Real.log (1 + frob x))) := by
  obtain ⟨N, hN⟩ := gauge_any hVabs hV
  refine ⟨N, fun M => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN (((t + 1) + 2 * (t + 1) * (r - (t + 1))) * M)
  refine ⟨C, hC, fun y k x => ?_⟩
  have hα : alpha (rectangularPoint h (torus y * (k : Langlands.GeneralLinear (t + 1) ℝ)) x) =
      fun i => zc y k x (Fin.cast (rect_size h).symm i) := by
    rw [rectangularPoint_eq]
    exact alpha_reindex_finCongr (rect_size h) _
  refine (hb _).trans ?_
  rw [hα, rootPos_cast (rect_size h), sum_abs_cast (rect_size h)]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
  have hdec := decay_le y k x
  have hgr := sum_abs_le y k x
  have hR := rootPos_nonneg (zc y k x)
  push_cast at hdec hgr ⊢
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 := mul_le_mul_of_nonneg_left hdec hM
  have h2 := mul_le_mul_of_nonneg_left hgr hN0
  nlinarith

/-! ### Elementary estimates -/

theorem coord_le {u A τ M : ℝ} (_hA : 0 ≤ A) (hτ : A + 1 ≤ τ) (hM : A + τ + 1 ≤ M) :
    -M * max u 0 + A * |u| + τ * u ≤ -|u| := by
  rcases le_or_gt 0 u with hu | hu
  · rw [max_eq_left hu, abs_of_nonneg hu]
    nlinarith
  · rw [max_eq_right hu.le, abs_of_neg hu]
    nlinarith

theorem sum_coord_le {n : ℕ} (y : Fin n → ℝ) {A τ M : ℝ} (hA : 0 ≤ A) (hτ : A + 1 ≤ τ)
    (hM : A + τ + 1 ≤ M) :
    -M * ∑ j, max (y j) 0 + A * ∑ j, |y j| + τ * ∑ j, y j ≤ -∑ j, |y j| := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum fun j _ => coord_le hA hτ hM

/-- The rectangular decay function `∏_(l,p) (1 + x_(lp)²)⁻¹`. -/
def rectDecay {d a : ℕ} (x : Matrix (Fin d) (Fin a) ℝ) : ℝ := ∏ l, ∏ p, (1 + x l p ^ 2)⁻¹

theorem exp_neg_mul_log_le {d a : ℕ} (x : Matrix (Fin d) (Fin a) ℝ) {κ : ℝ}
    (hκ : (a : ℝ) * d ≤ κ) : Real.exp (-κ * Real.log (1 + frob x)) ≤ rectDecay x := by
  have hS := frob_nonneg x
  have hpos : 0 < 1 + frob x := by linarith
  have hΛ : 0 ≤ Real.log (1 + frob x) := Real.log_nonneg (by linarith)
  have h1 : Real.exp (-κ * Real.log (1 + frob x)) ≤
      Real.exp (-((a * d : ℕ) : ℝ) * Real.log (1 + frob x)) := by
    refine Real.exp_le_exp.mpr ?_
    push_cast
    nlinarith
  refine h1.trans ?_
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hpos]
  have hle : ∏ l : Fin d, ∏ p : Fin a, (1 + x l p ^ 2) ≤ (1 + frob x) ^ (a * d) := by
    calc
      ∏ l : Fin d, ∏ p : Fin a, (1 + x l p ^ 2) ≤ ∏ _l : Fin d, ∏ _p : Fin a, (1 + frob x) := by
        refine Finset.prod_le_prod₀ (fun l _ => Finset.prod_nonneg fun p _ => by positivity)
          fun l _ => Finset.prod_le_prod₀ (fun p _ => by positivity) fun p _ => ?_
        have h1 : x l p ^ 2 ≤ ∑ p, x l p ^ 2 :=
          Finset.single_le_sum (f := fun p => x l p ^ 2) (fun p _ => sq_nonneg _)
            (Finset.mem_univ p)
        have h2 : ∑ p, x l p ^ 2 ≤ frob x :=
          Finset.single_le_sum (f := fun l => ∑ p, x l p ^ 2)
            (fun l _ => Finset.sum_nonneg fun p _ => sq_nonneg _) (Finset.mem_univ l)
        linarith
      _ = (1 + frob x) ^ (a * d) := by
        rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Finset.card_univ,
          Fintype.card_fin, Fintype.card_fin, ← pow_mul, mul_comm]
  have hP : 0 < ∏ l : Fin d, ∏ p : Fin a, (1 + x l p ^ 2) :=
    Finset.prod_pos fun l _ => Finset.prod_pos fun p _ => by positivity
  have hD : rectDecay x = (∏ l : Fin d, ∏ p : Fin a, (1 + x l p ^ 2))⁻¹ := by
    unfold rectDecay
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun l _ => Finset.prod_inv_distrib _
  rw [hD]
  exact inv_anti₀ hP hle

theorem sigmaFinite_haar (ν : AdditiveHaarMeasure ℝ) : SigmaFinite ν.measure := by
  rw [Measure.isAddLeftInvariant_eq_smul_of_regular ν.measure volume]
  infer_instance

theorem integrable_inv_one_add_sq_haar (ν : AdditiveHaarMeasure ℝ) :
    Integrable (fun v : ℝ => (1 + v ^ 2)⁻¹) ν.measure := by
  rw [Measure.isAddLeftInvariant_eq_smul_of_regular ν.measure volume]
  exact integrable_inv_one_add_sq.smul_measure ENNReal.coe_ne_top

theorem sigmaFinite_rect (ν : AdditiveHaarMeasure ℝ) (d a : ℕ) :
    SigmaFinite (rectangularMeasure ν d a) := by
  have := sigmaFinite_haar ν
  have h : SigmaFinite (Measure.pi (fun _ : Fin d => Measure.pi fun _ : Fin a => ν.measure)) :=
    inferInstance
  exact h

theorem integrable_rectDecay (ν : AdditiveHaarMeasure ℝ) (d a : ℕ) :
    Integrable (fun x : Matrix (Fin d) (Fin a) ℝ => rectDecay x) (rectangularMeasure ν d a) := by
  have := sigmaFinite_haar ν
  unfold rectangularMeasure rectDecay
  exact Integrable.fintype_prod (f := fun _ (v : Fin a → ℝ) => ∏ p, (1 + v p ^ 2)⁻¹) fun _ =>
    Integrable.fintype_prod (f := fun _ (u : ℝ) => (1 + u ^ 2)⁻¹) fun _ =>
      integrable_inv_one_add_sq_haar ν

theorem rectDecay_nonneg {d a : ℕ} (x : Matrix (Fin d) (Fin a) ℝ) : 0 ≤ rectDecay x :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => by positivity

theorem continuous_rectDecay {d a : ℕ} : Continuous (rectDecay (d := d) (a := a)) := by
  unfold rectDecay
  refine continuous_finsetProd _ fun l _ => continuous_finsetProd _ fun p _ => ?_
  refine Continuous.inv₀ (by fun_prop) fun x => by positivity

/-! ### Integrability criteria -/

theorem integrable_exp_comp_alphaQ {ν : Measure (LeftUnipotentQuotient t ℝ)} {κ : ℝ≥0}
    {L : (Fin (t + 1) → ℝ) →L[ℝ] ℝ}
    (hκL : ∀ B : (Fin (t + 1) → ℝ) → ℝ≥0∞, Measurable B →
      ∫⁻ q, B (alphaQ q) ∂ν = (κ : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (Real.exp (L x)) * B x)
    {E : (Fin (t + 1) → ℝ) → ℝ} (hE : Continuous E)
    (hEL : ∀ y, L y + E y ≤ -∑ j, |y j|) :
    Integrable (fun q => Real.exp (E (alphaQ q))) ν := by
  refine ⟨(Real.continuous_exp.comp (hE.comp continuous_alphaQ)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun q => (Real.exp_pos _).le)]
  have hBm : Measurable fun y => ENNReal.ofReal (Real.exp (E y)) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp hE).measurable
  calc
    ∫⁻ q, ENNReal.ofReal (Real.exp (E (alphaQ q))) ∂ν =
        (κ : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (Real.exp (L x)) *
          ENNReal.ofReal (Real.exp (E x)) := hκL _ hBm
    _ ≤ (κ : ℝ≥0∞) * ∫⁻ x : Fin (t + 1) → ℝ,
          ENNReal.ofReal (Real.exp (-1 * ∑ j, |x j|)) := by
      refine mul_le_mul_right (lintegral_mono fun x => ?_) _
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [hEL x]))
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top (lintegral_exp_neg_mul_sum_abs_lt_top one_pos)

/-! ### Convergence and holomorphy of the dual block integral -/

/-- The kernel `(g, x) ↦ V(rect(g, x)) V'(g)` of the block integral. -/
def bkernel (h : t < r) (V : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (V' : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
    (p : Langlands.GeneralLinear (t + 1) ℝ × Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ) : ℂ :=
  V (rectangularPoint h p.1 p.2) * V' p.1

theorem continuous_rectangularPoint (h : t < r) :
    Continuous (fun p : Langlands.GeneralLinear (t + 1) ℝ ×
      Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ => rectangularPoint h p.1 p.2) := by
  have h0 : Continuous fun p : Langlands.GeneralLinear (t + 1) ℝ ×
      Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ =>
      ((p.1, p.2, (1 : Langlands.GeneralLinear.lowerTriangularSubgroup (r - (t + 1)) ℝ)) :
        Langlands.GeneralLinear.LowerBlockParameters (t + 1) (r - (t + 1)) ℝ) :=
    continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
  have h1 := (Langlands.GeneralLinear.continuous_lowerBlockLocalization (a := t + 1)
    (d := r - (t + 1)) (R := ℝ) 1).comp h0
  have h2 := (Langlands.GeneralLinear.reindexContinuous (R := ℝ)
    (finCongr (rect_size h))).continuous.comp h1
  exact h2

set_option maxHeartbeats 1600000 in
/-- **Convergence and holomorphy of the real dual block integral.** Let `t < r`, let `V` on
`GL_(r+1)(ℝ)` and `V'` on `GL_(t+1)(ℝ)` be continuous and satisfy the gauge estimate, let `‖V‖`
be left invariant under the upper unipotent group, and let the kernel
`V(rect(g, x)) V'(g)` be left invariant in `g` under the upper unipotent group of `GL_(t+1)(ℝ)`.
Then there is `σ` such that for `Re s > σ` the block kernel is integrable for the product of the
quotient measure and the rectangular measure, and the block integral is holomorphic there. -/
theorem exists_dual_convergence (h : t < r) (D : RealQuotientMeasureData t)
    (ν : AdditiveHaarMeasure ℝ)
    {V : Langlands.GeneralLinear (r + 1) ℝ → ℂ} {V' : Langlands.GeneralLinear (t + 1) ℝ → ℂ}
    (hV : Continuous V) (hV' : Continuous V')
    (hVabs : ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g, ‖V (u * g)‖ = ‖V g‖)
    (hinv : ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ, ∀ g x,
      bkernel h V V' (u * g, x) = bkernel h V V' (g, x))
    (hgV : HasGauge V) (hgV' : HasGauge V') :
    ∃ σ : ℝ, (∀ s : ℂ, σ < s.re →
        Integrable (fun p => blockKernel realNormalizedAbs h V V' s p.1 p.2)
          (D.measure.prod (rectangularMeasure ν (r - (t + 1)) (t + 1)))) ∧
      DifferentiableOn ℂ (blockIntegral realNormalizedAbs D.measure ν h V V')
        {s : ℂ | σ < s.re} := by
  have := D.groupHaar_isHaar
  have := D.unipotentHaar_isHaar
  have := D.unipotentHaar_rightInvariant
  obtain ⟨κ, L, hκL⟩ :=
    exists_lintegral_alphaQ D.groupHaar D.unipotentHaar D.measure D.compatible
  set ρ := rectangularMeasure ν (r - (t + 1)) (t + 1) with hρ
  have hρσ : SigmaFinite ρ := sigmaFinite_rect ν _ _
  obtain ⟨N1, hN1⟩ := rect_bound h hVabs hgV
  obtain ⟨N2, hN2⟩ := hgV'
  obtain ⟨C2, hC2, hb2⟩ := hN2 0
  set A : ℝ := (N1 : ℝ) + N2 + ‖L‖ with hA
  have hA0 : 0 ≤ A := by positivity
  -- the orthogonal coordinate on the quotient
  have hkinv : ∀ u : Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ, ∀ g,
      kpart (u.val * g) = kpart g := fun u g => kpart_unipotent_mul u g
  set kQ := descend (Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ) kpart hkinv with hkQ
  have hkQc : Continuous kQ := by
    rw [hkQ]
    unfold descend
    exact continuous_kpart.quotient_lift _
  have hkout : ∀ q : LeftUnipotentQuotient t ℝ, kpart q.out = kQ q :=
    fun q => out_eq_descend kpart hkinv q
  let sec : LeftUnipotentQuotient t ℝ → Langlands.GeneralLinear (t + 1) ℝ :=
    fun q => torus (alphaQ q) * (kQ q : Langlands.GeneralLinear (t + 1) ℝ)
  have hsec : Continuous sec :=
    (continuous_torus.comp continuous_alphaQ).mul (continuous_subtype_val.comp hkQc)
  -- the kernel on the quotient
  let f : LeftUnipotentQuotient t ℝ × Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ → ℂ :=
    fun p => bkernel h V V' (p.1.out, p.2)
  have hfsec : ∀ p, f p = bkernel h V V' (sec p.1, p.2) := by
    rintro ⟨q, x⟩
    have hK : ∀ u : Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ, ∀ g,
        (fun g => bkernel h V V' (g, x)) (u.val * g) = (fun g => bkernel h V V' (g, x)) g :=
      fun u g => hinv u.val u.2 g x
    have := eq_torus_mul_kpart (fun g => bkernel h V V' (g, x)) hK q.out
    show bkernel h V V' (q.out, x) =
      bkernel h V V' (torus (alphaQ q) * (kQ q : Langlands.GeneralLinear (t + 1) ℝ), x)
    rw [← alpha_out q, ← hkout q]
    exact this
  have hbkc : Continuous (bkernel h V V') :=
    (hV.comp (continuous_rectangularPoint h)).mul (hV'.comp continuous_fst)
  have hfc : Continuous f := by
    have : f = fun p => bkernel h V V' (sec p.1, p.2) := funext hfsec
    rw [this]
    exact hbkc.comp ((hsec.comp continuous_fst).prodMk continuous_snd)
  have hlinv : ∀ u : Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ, ∀ g,
      logDet (u.val * g) = logDet g := fun u g => logDet_unipotent_mul u g
  let ℓ : LeftUnipotentQuotient t ℝ → ℝ := fun q => logDet q.out
  have hℓc : Continuous ℓ := by
    have hℓe : ℓ = descend (Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ)
        logDet hlinv := funext fun q => out_eq_descend _ hlinv q
    rw [hℓe]
    exact continuous_descend_real hlinv continuous_logDet
  have hℓq : ∀ q, ℓ q = ∑ j, alphaQ q j := by
    intro q
    rw [← alpha_out q, ← logDet_torus_mul (alpha q.out) (kpart q.out)]
    exact eq_torus_mul_kpart logDet hlinv q.out
  -- the main pointwise bound
  have hbound : ∀ τ : ℝ, A + 1 ≤ τ → ∃ C : ℝ, 0 ≤ C ∧ ∃ E : (Fin (t + 1) → ℝ) → ℝ,
      Continuous E ∧ (∀ y, L y + E y ≤ -∑ j, |y j|) ∧
      ∀ q x, ‖f (q, x)‖ * Real.exp (τ * ℓ q) ≤ C * Real.exp (E (alphaQ q)) * rectDecay x := by
    intro τ hτ
    set M : ℕ := ⌈A + τ + 1 + 2 * (N1 : ℝ) * (((t : ℝ) + 1) + ((r - (t + 1) : ℕ) : ℝ)) +
      2 * ((t : ℝ) + 1) * ((r - (t + 1) : ℕ) : ℝ)⌉₊ with hM
    have hMle := Nat.le_ceil (A + τ + 1 + 2 * (N1 : ℝ) * (((t : ℝ) + 1) +
      ((r - (t + 1) : ℕ) : ℝ)) + 2 * ((t : ℝ) + 1) * ((r - (t + 1) : ℕ) : ℝ))
    rw [← hM] at hMle
    have hN10 : (0 : ℝ) ≤ N1 := Nat.cast_nonneg N1
    have hd0 : (0 : ℝ) ≤ ((r - (t + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    obtain ⟨C1, hC1, hb1⟩ := hN1 M
    refine ⟨C1 * C2, mul_nonneg hC1 hC2, fun y => -(M : ℝ) * ∑ j, max (y j) 0 +
      ((N1 : ℝ) + N2) * ∑ j, |y j| + τ * ∑ j, y j, ?_, ?_, ?_⟩
    · have h1 : Continuous fun y : Fin (t + 1) → ℝ => ∑ j, max (y j) 0 :=
        continuous_finsetSum _ fun j _ => (continuous_apply j).max continuous_const
      have h2 : Continuous fun y : Fin (t + 1) → ℝ => ∑ j, |y j| :=
        continuous_finsetSum _ fun j _ => (continuous_apply j).abs
      have h3 : Continuous fun y : Fin (t + 1) → ℝ => ∑ j, y j :=
        continuous_finsetSum _ fun j _ => continuous_apply j
      exact ((continuous_const.mul h1).add (continuous_const.mul h2)).add (continuous_const.mul h3)
    · intro y
      have h1 := linear_le L y
      have h2 := sum_coord_le y hA0 hτ (M := (M : ℝ)) (by nlinarith)
      rw [hA] at h2
      nlinarith
    · intro q x
      set y := alphaQ q with hy
      set k := kQ q with hk
      have hfe : f (q, x) = V (rectangularPoint h (torus y * (k : Langlands.GeneralLinear (t + 1) ℝ)) x) *
          V' (torus y * (k : Langlands.GeneralLinear (t + 1) ℝ)) := hfsec (q, x)
      rw [hfe, hℓq q, norm_mul]
      have h1 := hb1 y k x
      have h2 := hb2 y k
      have hκ : (((t + 1 : ℕ) : ℝ)) * ((r - (t + 1) : ℕ) : ℝ) ≤
          (M : ℝ) * ((t : ℝ) + 1) / 2 -
            (N1 : ℝ) * (((t : ℝ) + 1) + ((r - (t + 1) : ℕ) : ℝ)) := by
        push_cast
        nlinarith
      have hx := exp_neg_mul_log_le x hκ
      have hS := frob_nonneg x
      set Λ := Real.log (1 + frob x) with hΛ
      have hexp : Real.exp (-(M : ℝ) * (∑ j, max (y j) 0 + ((t : ℝ) + 1) * Λ / 2) +
            (N1 : ℝ) * (∑ j, |y j| + (((t : ℝ) + 1) + ((r - (t + 1) : ℕ) : ℝ)) * Λ)) *
          Real.exp (-((0 : ℕ) : ℝ) * rootPos y + (N2 : ℝ) * ∑ j, |y j|) *
          Real.exp (τ * ∑ j, y j) =
          Real.exp (-(M : ℝ) * ∑ j, max (y j) 0 + ((N1 : ℝ) + N2) * ∑ j, |y j| +
            τ * ∑ j, y j) *
          Real.exp (-((M : ℝ) * ((t : ℝ) + 1) / 2 -
            (N1 : ℝ) * (((t : ℝ) + 1) + ((r - (t + 1) : ℕ) : ℝ))) * Λ) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        push_cast
        ring
      calc
        ‖V (rectangularPoint h (torus y * (k : Langlands.GeneralLinear (t + 1) ℝ)) x)‖ *
            ‖V' (torus y * (k : Langlands.GeneralLinear (t + 1) ℝ))‖ *
            Real.exp (τ * ∑ j, y j) ≤
            (C1 * Real.exp (-(M : ℝ) * (∑ j, max (y j) 0 + ((t : ℝ) + 1) * Λ / 2) +
              (N1 : ℝ) * (∑ j, |y j| + (((t : ℝ) + 1) + ((r - (t + 1) : ℕ) : ℝ)) * Λ))) *
            (C2 * Real.exp (-((0 : ℕ) : ℝ) * rootPos y + (N2 : ℝ) * ∑ j, |y j|)) *
            Real.exp (τ * ∑ j, y j) := by
          gcongr
        _ = C1 * C2 * (Real.exp (-(M : ℝ) * ∑ j, max (y j) 0 + ((N1 : ℝ) + N2) * ∑ j, |y j| +
              τ * ∑ j, y j) *
            Real.exp (-((M : ℝ) * ((t : ℝ) + 1) / 2 -
              (N1 : ℝ) * (((t : ℝ) + 1) + ((r - (t + 1) : ℕ) : ℝ))) * Λ)) := by
          rw [← hexp]
          ring
        _ ≤ C1 * C2 * (Real.exp (-(M : ℝ) * ∑ j, max (y j) 0 + ((N1 : ℝ) + N2) * ∑ j, |y j| +
              τ * ∑ j, y j) * rectDecay x) := by
          gcongr
        _ = _ := by ring
  -- integrability of the weighted kernel on the product
  have hfm : AEStronglyMeasurable f (D.measure.prod ρ) := hfc.aestronglyMeasurable
  have hintP : ∀ τ : ℝ, A + 1 ≤ τ →
      Integrable (fun p => ‖f p‖ * Real.exp (τ * ℓ p.1)) (D.measure.prod ρ) := by
    intro τ hτ
    obtain ⟨C, hC, E, hE, hEL, hb⟩ := hbound τ hτ
    have hI := ((integrable_exp_comp_alphaQ hκL hE hEL).const_mul C).mul_prod
      (integrable_rectDecay ν (r - (t + 1)) (t + 1))
    refine hI.mono' ((hfc.norm.mul (Real.continuous_exp.comp
      (continuous_const.mul (hℓc.comp continuous_fst)))).aestronglyMeasurable)
      (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
    exact hb p.1 p.2
  set c0 : ℝ := ((r - t : ℕ) : ℝ) / 2 with hc0
  have hker : ∀ s : ℂ, (fun p : LeftUnipotentQuotient t ℝ ×
      Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ => blockKernel realNormalizedAbs h V V' s p.1 p.2) =
      fun p => f p * Complex.exp ((s - ((r - t : ℕ) : ℂ) / 2) * (ℓ p.1 : ℂ)) := by
    intro s
    rfl
  have hnormk : ∀ (s : ℂ) p, ‖f p * Complex.exp ((s - ((r - t : ℕ) : ℂ) / 2) * (ℓ p.1 : ℂ))‖ =
      ‖f p‖ * Real.exp ((s.re - c0) * ℓ p.1) := by
    intro s p
    rw [norm_mul, norm_cexp_mul_ofReal, hc0]
    congr 3
    simp
  refine ⟨A + 1 + c0, fun s hs => ?_, ?_⟩
  · rw [hker s]
    refine (hintP (s.re - c0) (by linarith)).mono'
      ((hfc.mul (Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp (hℓc.comp continuous_fst))))).aestronglyMeasurable)
      (ae_of_all _ fun p => ?_)
    rw [hnormk]
  · -- the inner integral
    let F : LeftUnipotentQuotient t ℝ → ℂ := fun q =>
      (∫ x, f (q, x) ∂ρ) * Complex.exp (-(((r - t : ℕ) : ℂ) / 2) * (ℓ q : ℂ))
    have hFm0 : AEStronglyMeasurable (fun q => ∫ x, f (q, x) ∂ρ) D.measure :=
      hfm.integral_prod_right'
    have hFm : AEStronglyMeasurable F D.measure :=
      hFm0.mul (Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp hℓc))).aestronglyMeasurable
    have hblock : blockIntegral realNormalizedAbs D.measure ν h V V' =
        fun s => ∫ q, F q * Complex.exp (s * (ℓ q : ℂ)) ∂D.measure := by
      funext s
      show ∫ q, ∫ x, f (q, x) * Complex.exp ((s - ((r - t : ℕ) : ℂ) / 2) * (ℓ q : ℂ)) ∂ρ
          ∂D.measure = _
      refine integral_congr_ae (ae_of_all _ fun q => ?_)
      show ∫ x, f (q, x) * Complex.exp ((s - ((r - t : ℕ) : ℂ) / 2) * (ℓ q : ℂ)) ∂ρ =
        (∫ x, f (q, x) ∂ρ) * Complex.exp (-(((r - t : ℕ) : ℂ) / 2) * (ℓ q : ℂ)) *
          Complex.exp (s * (ℓ q : ℂ))
      rw [integral_mul_const, mul_assoc, ← Complex.exp_add]
      congr 2
      ring
    rw [hblock]
    refine differentiableOn_integral_cexp_mul hFm hℓc.aestronglyMeasurable fun τ' hτ' => ?_
    have hτ : A + 1 ≤ τ' - c0 := by linarith
    obtain ⟨C, hC, E, hE, hEL, hb⟩ := hbound (τ' - c0) hτ
    set I := ∫ x, rectDecay x ∂ρ with hI
    have hbd := ((integrable_exp_comp_alphaQ hκL hE hEL).const_mul C).mul_const I
    refine hbd.mono' ((hFm.norm.mul (Real.continuous_exp.comp
      (continuous_const.mul hℓc)).aestronglyMeasurable)) (ae_of_all _ fun q => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
    have hnF : ‖F q‖ * Real.exp (τ' * ℓ q) =
        ‖∫ x, f (q, x) ∂ρ‖ * Real.exp ((τ' - c0) * ℓ q) := by
      show ‖(∫ x, f (q, x) ∂ρ) * Complex.exp (-(((r - t : ℕ) : ℂ) / 2) * (ℓ q : ℂ))‖ *
        Real.exp (τ' * ℓ q) = _
      rw [norm_mul, norm_cexp_mul_ofReal, mul_assoc, ← Real.exp_add, hc0]
      congr 2
      simp
      ring
    rw [hnF]
    have hint_x : Integrable (fun x => C * Real.exp (E (alphaQ q)) * rectDecay x) ρ :=
      (integrable_rectDecay ν (r - (t + 1)) (t + 1)).const_mul _
    calc
      ‖∫ x, f (q, x) ∂ρ‖ * Real.exp ((τ' - c0) * ℓ q) ≤
          (∫ x, ‖f (q, x)‖ ∂ρ) * Real.exp ((τ' - c0) * ℓ q) :=
        mul_le_mul_of_nonneg_right (norm_integral_le_integral_norm _) (Real.exp_pos _).le
      _ = ∫ x, ‖f (q, x)‖ * Real.exp ((τ' - c0) * ℓ q) ∂ρ := (integral_mul_const _ _).symm
      _ ≤ ∫ x, C * Real.exp (E (alphaQ q)) * rectDecay x ∂ρ :=
        integral_mono_of_nonneg (ae_of_all _ fun x =>
          mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) hint_x (ae_of_all _ fun x => hb q x)
      _ = C * Real.exp (E (alphaQ q)) * I := by rw [integral_const_mul]

end Langlands.Global.RankinSelbergGlobal.RealUnequalDualConvergence
