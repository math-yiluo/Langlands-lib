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

/-- The real toral gauge exponent is controlled by the positive comparison coordinates
and the logarithm of the squared rectangular norm. -/
theorem rectangular_toralExponent_le (h : t < r) (M N : ℕ)
    (y : Fin (t + 1) → ℝ) (k : unitaryCompact ℝ (t + 1))
    (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ) :
    let z := alpha (rectangularPoint h (torus y * k.val) x);
    -((((t + 1) + 2 * (t + 1) * (r - (t + 1))) * M : ℕ) : ℝ) * rootPos z +
        (N : ℝ) * ∑ j, |z j| ≤
      -(M : ℝ) * (∑ j, max (y j) 0 + ((t : ℝ) + 1) * Real.log (1 + frob x) / 2) +
        (N : ℝ) * (∑ j, |y j| + (((t : ℝ) + 1) + ((r - (t + 1) : ℕ) : ℝ)) * Real.log (1 + frob x)) := by
  dsimp only
  have hα : alpha (rectangularPoint h (torus y * (k : Langlands.GeneralLinear (t + 1) ℝ)) x) =
      fun i => zc y k x (Fin.cast (rect_size h).symm i) := by
    rw [rectangularPoint_eq]
    exact alpha_reindex_finCongr (rect_size h) _
  rw [hα, rootPos_cast (rect_size h), sum_abs_cast (rect_size h)]
  have hdec := decay_le y k x
  have hgr := sum_abs_le y k x
  have hR := rootPos_nonneg (zc y k x)
  push_cast at hdec hgr ⊢
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 := mul_le_mul_of_nonneg_left hdec hM
  have h2 := mul_le_mul_of_nonneg_left hgr hN0
  nlinarith

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
  exact (hb _).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (rectangular_toralExponent_le h M N y k x)) hC)

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

theorem integrable_exp_comp_alphaQ_of_le {ν : Measure (LeftUnipotentQuotient t ℝ)} {κ : ℝ≥0}
    {L : (Fin (t + 1) → ℝ) →L[ℝ] ℝ}
    (hκL : ∀ B : (Fin (t + 1) → ℝ) → ℝ≥0∞, Measurable B →
      ∫⁻ q, B (alphaQ q) ∂ν = (κ : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (Real.exp (L x)) * B x)
    {E : (Fin (t + 1) → ℝ) → ℝ} (hE : Continuous E) {c : ℝ} (hc : 0 < c)
    (hEL : ∀ y, L y + E y ≤ -c * ∑ j, |y j|) :
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
          ENNReal.ofReal (Real.exp (-c * ∑ j, |x j|)) := by
      refine mul_le_mul_right (lintegral_mono fun x => ?_) _
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hEL x))
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top (lintegral_exp_neg_mul_sum_abs_lt_top hc)

theorem integrable_exp_comp_alphaQ {ν : Measure (LeftUnipotentQuotient t ℝ)} {κ : ℝ≥0}
    {L : (Fin (t + 1) → ℝ) →L[ℝ] ℝ}
    (hκL : ∀ B : (Fin (t + 1) → ℝ) → ℝ≥0∞, Measurable B →
      ∫⁻ q, B (alphaQ q) ∂ν = (κ : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (Real.exp (L x)) * B x)
    {E : (Fin (t + 1) → ℝ) → ℝ} (hE : Continuous E)
    (hEL : ∀ y, L y + E y ≤ -∑ j, |y j|) :
    Integrable (fun q => Real.exp (E (alphaQ q))) ν :=
  integrable_exp_comp_alphaQ_of_le hκL hE one_pos (by simpa using hEL)

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

local notation "G" => fun m : ℕ => Langlands.GeneralLinear (m + 1) ℝ
local notation "Q" => fun m : ℕ => LeftUnipotentQuotient m ℝ
local notation "Rect" => fun m d : ℕ => Matrix (Fin d) (Fin (m + 1)) ℝ

/-- The rectangular kernel bound after separating a fixed integrable rectangle weight. -/
def HasRectangularToralBound {d : ℕ} (A : ℝ) (F : G t × Rect t d → ℂ) : Prop :=
  ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (y : Fin (t + 1) → ℝ) (k : unitaryCompact ℝ (t + 1)) (x : Rect t d),
      ‖F (torus y * k.val, x)‖ ≤
        C * Real.exp (-(M : ℝ) * ∑ j, max (y j) 0 + A * ∑ j, |y j|) * rectDecay x

/-- Arbitrarily high joint decay in the positive toral coordinates and the rectangular variable
supplies the fixed integrable rectangular weight. -/
theorem hasRectangularToralBound_of_log_bound {d : ℕ} {A B : ℝ} {F : G t × Rect t d → ℂ}
    (hF : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (y : Fin (t + 1) → ℝ) (k : unitaryCompact ℝ (t + 1)) (x : Rect t d),
        ‖F (torus y * k.val, x)‖ ≤
          C * Real.exp (-(M : ℝ) * ∑ j, max (y j) 0 + A * ∑ j, |y j| +
            (B - (M : ℝ) * ((t : ℝ) + 1) / 2) * Real.log (1 + frob x))) :
    HasRectangularToralBound A F := by
  intro M
  let B' : ℝ := 2 * (B + ((t : ℝ) + 1) * d)
  let M' : ℕ := M + ⌈B'⌉₊
  have hM' : (M : ℝ) ≤ M' := by exact_mod_cast Nat.le_add_right M _
  have hM'' : B' ≤ (M' : ℝ) := (Nat.le_ceil B').trans (by
    simp only [M', Nat.cast_add]
    exact le_add_of_nonneg_left (Nat.cast_nonneg M))
  have hRank : (1 : ℝ) ≤ (t : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg t)
  have hExtra : (M' : ℝ) ≤ (M' : ℝ) * ((t : ℝ) + 1) :=
    le_mul_of_one_le_right (Nat.cast_nonneg M') hRank
  obtain ⟨C, hC, H⟩ := hF M'
  refine ⟨C, hC, fun y k x => (H y k x).trans ?_⟩
  have hDim : ((t + 1 : ℕ) : ℝ) * d ≤ (M' : ℝ) * ((t : ℝ) + 1) / 2 - B := by
    dsimp [B'] at hM''
    push_cast
    linarith
  have hx := exp_neg_mul_log_le x hDim
  have hy : -(M' : ℝ) * ∑ j, max (y j) 0 ≤ -(M : ℝ) * ∑ j, max (y j) 0 :=
    mul_le_mul_of_nonneg_right (neg_le_neg hM') (Finset.sum_nonneg fun j _ => le_max_right _ _)
  rw [Real.exp_add, ← mul_assoc, ← neg_sub ((M' : ℝ) * ((t : ℝ) + 1) / 2) B]
  exact mul_le_mul (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith only [hy])) hC) hx (Real.exp_nonneg _) (by positivity)

/-- For fixed compatible quotient and rectangular measures, kernels of one fixed toral growth
exponent with the rectangular decay bound have a common half-plane of absolute convergence
and holomorphy. The determinant parameter is shifted by the given real number. -/
def RealRectangularToralConvergenceStatement : Prop :=
  ∀ (t d : ℕ) (D : RealQuotientMeasureData t) (ν : AdditiveHaarMeasure ℝ) (A c : ℝ), 0 ≤ A →
    ∃ σ : ℝ, ∀ (F : G t × Rect t d → ℂ), Continuous F →
      (∀ (u : Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ) g x, F (u.val * g, x) = F (g, x)) →
      HasRectangularToralBound A F →
      (∀ s : ℂ, σ < s.re → Integrable (fun p : Q t × Rect t d =>
        F (p.1.out, p.2) * Complex.exp ((s - c) * (logDet p.1.out : ℂ)))
        (D.measure.prod (rectangularMeasure ν d (t + 1)))) ∧
      DifferentiableOn ℂ (fun s : ℂ => ∫ p : Q t × Rect t d,
        F (p.1.out, p.2) * Complex.exp ((s - c) * (logDet p.1.out : ℂ))
          ∂(D.measure.prod (rectangularMeasure ν d (t + 1)))) {s | σ < s.re}

set_option maxHeartbeats 1000000 in
theorem realRectangularToralConvergence : RealRectangularToralConvergenceStatement := by
  intro t d D ν A c hA
  have := D.groupHaar_isHaar
  have := D.unipotentHaar_isHaar
  have := D.unipotentHaar_rightInvariant
  obtain ⟨κ, L, hκL⟩ := exists_lintegral_alphaQ D.groupHaar D.unipotentHaar D.measure D.compatible
  let ρ := rectangularMeasure ν d (t + 1)
  have hρ : SigmaFinite ρ := sigmaFinite_rect ν _ _
  let σ₀ := A + ‖L‖ + 1
  let kQ := descend (Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ) kpart kpart_unipotent_mul
  have hkQc : Continuous kQ := continuous_kpart.quotient_lift _
  let sec (q : Q t) : G t := torus (alphaQ q) * (kQ q).val
  have hsec : Continuous sec :=
    (continuous_torus.comp continuous_alphaQ).mul (continuous_subtype_val.comp hkQc)
  refine ⟨σ₀ + c, fun F hF hInv hBound => ?_⟩
  let f (p : Q t × Rect t d) := F (p.1.out, p.2)
  have hfsec (q : Q t) (x : Rect t d) : f (q, x) = F (sec q, x) := by
    have hkout : kpart q.out = kQ q := out_eq_descend kpart kpart_unipotent_mul q
    change F (q.out, x) = F (torus (alphaQ q) * (kQ q).val, x)
    rw [← alpha_out q, ← hkout]
    exact eq_torus_mul_kpart (fun g => F (g, x)) (fun u g => hInv u g x) q.out
  have hfc : Continuous f := by
    rw [show f = fun p => F (sec p.1, p.2) from funext fun p => hfsec p.1 p.2]
    exact hF.comp ((hsec.comp continuous_fst).prodMk continuous_snd)
  let ℓ (p : Q t × Rect t d) := logDet p.1.out
  have hℓc : Continuous ℓ := by
    have he (q : Q t) := out_eq_descend logDet logDet_unipotent_mul q
    simp_rw [ℓ, he]
    exact (continuous_descend_real logDet_unipotent_mul continuous_logDet).comp continuous_fst
  have hℓq (q : Q t) (x : Rect t d) : ℓ (q, x) = ∑ j, alphaQ q j := by
    rw [← alpha_out q, ← logDet_torus_mul (alpha q.out) (kpart q.out)]
    exact eq_torus_mul_kpart logDet logDet_unipotent_mul q.out
  have hint (τ : ℝ) (hτ : σ₀ < τ) :
      Integrable (fun p => ‖f p‖ * Real.exp (τ * ℓ p)) (D.measure.prod ρ) := by
    let M : ℕ := ⌈σ₀ + τ⌉₊
    obtain ⟨C, hC, hb⟩ := hBound M
    let E (y : Fin (t + 1) → ℝ) := -(M : ℝ) * ∑ j, max (y j) 0 + A * ∑ j, |y j| + τ * ∑ j, y j
    have hEc : Continuous E := by
      unfold E
      fun_prop
    have hExp (y : Fin (t + 1) → ℝ) : L y + E y ≤ -∑ j, |y j| := by
      have hM : A + ‖L‖ + τ + 1 ≤ (M : ℝ) :=
        (show A + ‖L‖ + τ + 1 ≤ σ₀ + τ by dsimp [σ₀]; linarith).trans (Nat.le_ceil _)
      have hMajor := sum_coord_le y (A := A + ‖L‖) (by positivity) hτ.le hM
      dsimp only [E]
      linarith [linear_le L y]
    have hI := ((integrable_exp_comp_alphaQ hκL hEc hExp).const_mul C).mul_prod (integrable_rectDecay ν d (t + 1))
    refine hI.mono' ((hfc.norm.mul (Real.continuous_exp.comp (continuous_const.mul hℓc))).aestronglyMeasurable)
      (ae_of_all _ ?_)
    rintro ⟨q, x⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le), hfsec, hℓq]
    refine (mul_le_mul_of_nonneg_right (hb (alphaQ q) (kQ q) x) (Real.exp_pos _).le).trans_eq ?_
    simp only [E, Real.exp_add]
    ring
  let z (s : ℂ) : ℂ := s - c
  have hre (s : ℂ) (hs : σ₀ + c < s.re) : σ₀ < (z s).re := by
    change σ₀ < s.re - c
    linarith
  refine ⟨fun s hs => ?_, ?_⟩
  · refine (hint (z s).re (hre s hs)).mono'
      ((hfc.mul (Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp hℓc)))).aestronglyMeasurable) (ae_of_all _ fun p => ?_)
    show ‖f p * Complex.exp (z s * (ℓ p : ℂ))‖ ≤ ‖f p‖ * Real.exp ((z s).re * ℓ p)
    rw [norm_mul, norm_cexp_mul_ofReal]
  · have hHol := differentiableOn_integral_cexp_mul (f := f) (ℓ := ℓ) hfc.aestronglyMeasurable
      hℓc.aestronglyMeasurable hint
    exact hHol.comp (differentiable_id.sub_const (c : ℂ)).differentiableOn (fun s hs => hre s hs)

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
  obtain ⟨N1, hN1⟩ := rect_bound h hVabs hgV
  obtain ⟨N2, hN2⟩ := hgV'
  obtain ⟨C2, hC2, hb2⟩ := hN2 0
  let A : ℝ := (N1 : ℝ) + N2
  let B : ℝ := (N1 : ℝ) * (((t : ℝ) + 1) + ((r - (t + 1) : ℕ) : ℝ))
  have hA : 0 ≤ A := by positivity
  have hGauge : HasRectangularToralBound A (bkernel h V V') := by
    apply hasRectangularToralBound_of_log_bound (B := B)
    intro M
    obtain ⟨C1, hC1, hb1⟩ := hN1 M
    refine ⟨C1 * C2, mul_nonneg hC1 hC2, fun y k x => ?_⟩
    simp only [bkernel, norm_mul]
    refine (mul_le_mul (hb1 y k x) (hb2 y k) (norm_nonneg _) (by positivity)).trans_eq ?_
    rw [show ∀ x y : ℝ, (C1 * x) * (C2 * y) = C1 * C2 * (x * y) by intros; ring, ← Real.exp_add]
    congr 2
    simp only [Nat.cast_zero, neg_zero, zero_mul, zero_add, A, B]
    ring
  let c : ℝ := ((r - t : ℕ) : ℝ) / 2
  obtain ⟨σ, hConv⟩ := realRectangularToralConvergence t (r - (t + 1)) D ν A c hA
  have ⟨hI, hHol⟩ := hConv (bkernel h V V')
    ((hV.comp (continuous_rectangularPoint h)).mul (hV'.comp continuous_fst))
    (fun u g x => hinv u.val u.2 g x) hGauge
  let F (s : ℂ) (p : Q t × Rect t (r - (t + 1))) : ℂ := blockKernel realNormalizedAbs h V V' s p.1 p.2
  have he (s : ℂ) : F s = fun p =>
      bkernel h V V' (p.1.out, p.2) * Complex.exp ((s - c) * (logDet p.1.out : ℂ)) := by
    unfold c
    push_cast
    rfl
  simp_rw [← he] at hI hHol
  have : SigmaFinite D.measure := by
    have : SigmaCompactSpace (Q t) := by
      rw [← isSigmaCompact_univ_iff]
      have he' := RealIwasawa.alphaQ_preimage (n := t + 1) Set.univ
      rw [Set.preimage_univ, Set.univ_prod_univ, Set.image_univ] at he'
      rw [he']
      exact isSigmaCompact_range RealIwasawa.continuous_mk_torus_mul
    have := D.unipotentHaar_rightInvariant
    have := D.compatible.regular
    infer_instance
  have := sigmaFinite_rect ν (r - (t + 1)) (t + 1)
  refine ⟨σ, hI, hHol.congr fun s hs => ?_⟩
  exact (integral_prod (F s) (hI s hs)).symm

end Langlands.Global.RankinSelbergGlobal.RealUnequalDualConvergence
