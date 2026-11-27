import Langlands.Global.RankinSelberg.RealTemperedOrdinaryConvergence
import Langlands.Global.RankinSelberg.RealUniformCanonicalRange
import Langlands.Global.RankinSelberg.RealWhittakerUniformGrowth
import Langlands.Global.RankinSelberg.RealLocalCharacterGrowthInterfaces
import Langlands.Global.RankinSelberg.RealUnequalFamilyGauge
import Langlands.Analysis.SeveralComplex.SmallExponentialBoundary

/-! # The tempered Whittaker bound for real character lists -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open Langlands.Analysis.SeveralComplex
open Langlands.Whittaker (norm_standardCharacter)
open ArchimedeanLocal RealIwasawa RealGodement RealGodementProfiles
open PartialJacquet MeasureTheory Metric Set
open RealEqualDualConvergence (revNeg weylLong_torus_weylLong)
open RealUnequalFamily (exists_uniform_derivativeGrowth)

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "K" => unitaryCompact ℝ (r + 1)
local notation "U" => Matrix.unitaryGroup (Fin (r + 1)) ℝ
local notation "N" => Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "P" => (Fin (r + 1) → ℂ)
local notation "Y" => (Fin (r + 1) → ℝ)
local notation "L" => (Fin (r + 1) → Fin 2)
local notation "w" => Langlands.GeneralLinear.weylLong (r + 1) ℝ

private def deform (z : P) (t : ℂ) : P := fun i => z i - t * (i.val : ℂ)

private theorem deform_re (z : P) (hz : ∀ i, (z i).re = 0) (t : ℂ) (i : Fin (r + 1)) :
    (deform z t i).re = -(t.re * i.val) := by
  simp [deform, Complex.mul_re, hz]

private theorem deform_mem_chamber (z : P) (hz : ∀ i, (z i).re = 0) {t : ℂ} (ht : 0 < t.re) :
    deform z t ∈ realSpectralChamber r := by
  intro i
  rw [deform_re z hz, deform_re z hz]
  simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  nlinarith

private theorem differentiable_deform (z : P) : Differentiable ℂ (deform z) :=
  differentiable_pi.mpr fun i => (differentiable_const (c := z i)).sub (differentiable_id.mul_const _)

private theorem section_norm_torus_mul {p : L} {φ : U → ℂ} (hφ : IsCompactProfile p φ)
    (z : P) (y : Y) (g : G) :
    ‖standardSection z φ (torus y * g)‖ =
      Real.exp (torusModularLog (r + 1) y / 2 + ∑ i, y i * (z i).re) * ‖standardSection z φ g‖ := by
  let d (i : Fin (r + 1)) := Units.mk0 (Real.exp (y i)) (Real.exp_ne_zero _)
  have hd : Langlands.GeneralLinear.Iwasawa.diagonalUnits d = torus y := by
    apply Units.ext
    rfl
  have h := (standardSection_mem hφ z).1.1.2 d 1 g
  change standardSection z φ (Langlands.GeneralLinear.Iwasawa.diagonalUnits d * (1 : G) * g) = _ at h
  rw [mul_one, hd] at h
  rw [h, norm_mul, norm_principalSeriesCharacter
    (RealStrictCharacterLanglandsQuotient.isSignedPower (characterList p z))]
  congr 1
  simp only [d, Units.val_mk0, abs_of_pos (Real.exp_pos _), ← Real.exp_mul,
    realPositionExponent_characterList]
  rw [← Real.exp_sum, torusModularLog_apply, Finset.sum_div, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem rev_log (y : Y) : torusModularLog (r + 1) (fun i => y i.rev) =
    -torusModularLog (r + 1) y := by
  have h : revNeg (-y) = (fun i => y i.rev) := by
    funext i
    exact neg_neg _
  simpa only [h, map_neg] using torusModularLog_revNeg (-y)

private theorem section_norm_le_reference (φ : U → ℂ) {C : ℝ} (hC : ∀ k, ‖φ k‖ ≤ C) (z z' : P)
    (hz : ∀ i, (z i).re = (z' i).re) (g : G) (k : K) :
    ‖standardSection z φ (g * k.val)‖ ≤ C * ‖standardSection z' (1 : U → ℂ) g‖ := by
  rw [standardSection_eq, standardSection_eq]
  simp only [norm_mul, Complex.norm_exp, alpha_mul_unitary, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, zero_mul, sub_zero, hz,
    Pi.one_apply, mul_one]
  rw [mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC _) (Real.exp_pos _).le

private theorem constant_profile : IsCompactProfile (0 : L) (1 : U → ℂ) := by
  refine ⟨continuous_const, ?_, ?_⟩
  · have h : (Set.range fun _ : U => (1 : U → ℂ)) = {1} := by simp
    change FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun _ : U => (1 : U → ℂ)))
    rw [h]
    infer_instance
  · simp

private theorem integral_norm_comp_conj (a : ℝˣ) (y : Y) {B : N → ℝ} (hB : Integrable B (upperStepHaar r a)) :
    (∫ u, B (conjTorus (-y) u) ∂upperStepHaar r a) =
      Real.exp (torusModularLog (r + 1) y) * ∫ u, B u ∂upperStepHaar r a := by
  have := upperStepHaar_isHaar r a
  have hm : Measurable (conjTorus (-y)) := (continuous_conjTorus_right (-y)).measurable
  have hmap := map_conjTorus (upperStepHaar r a) (-y)
  have hBm : AEStronglyMeasurable B ((upperStepHaar r a).map (conjTorus (-y))) := by
    rw [hmap]
    exact hB.aestronglyMeasurable.smul_measure _
  rw [← integral_map hm.aemeasurable hBm, hmap, integral_smul_measure, ENNReal.toReal_ofReal
    (Real.exp_pos _).le, smul_eq_mul, map_neg, neg_neg]

private theorem torus_weyl_conj (y : Y) (u : N) (k : K) :
    w * u.val * (torus y * k.val) =
      torus (fun i => y i.rev) * ((w * (conjTorus (-y) u).val) * k.val) := by
  have hw := Langlands.GeneralLinear.weylLong_mul_self (r + 1) ℝ
  have hww (g : G) : w * torus y * w * (w * g) = w * torus y * g := by
    rw [mul_assoc (w * torus y) w (w * g), ← mul_assoc w w g, hw, one_mul]
  rw [← weylLong_torus_weylLong]
  change _ = w * torus y * w * (w * (torus (-y) * u.val * torus (-(-y))) * k.val)
  rw [← mul_assoc (w * torus y * w) _ k.val, hww, neg_neg, torus_neg]
  group

private theorem sum_abs_rev (y : Y) : ∑ i : Fin (r + 1), |y i.rev| = ∑ i, |y i| :=
  Equiv.sum_comp Fin.revPerm (fun i => |y i|)

private theorem sum_exponent_le (z : P) (hz : ∀ i, (z i).re = 0) {t : ℂ} (ht : 0 ≤ t.re)
    (y : Y) : ∑ i, y i * (deform z t i).re ≤ (r : ℝ) * t.re * ∑ i, |y i| := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [deform_re z hz]
  have hi : (i.val : ℝ) ≤ r := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  calc
    y i * -(t.re * i.val) = -y i * (t.re * i.val) := by ring
    _ ≤ |y i| * (t.re * i.val) :=
      mul_le_mul_of_nonneg_right (neg_le_abs _) (mul_nonneg ht (by positivity))
    _ ≤ |y i| * (t.re * r) := by gcongr
    _ = _ := by ring

private theorem canonical_bound_dominant_line (a : ℝˣ) {p : L} {φ : U → ℂ} (hφ : IsCompactProfile p φ)
    (z : P) (hz : ∀ i, (z i).re = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℂ, t.re = δ → ∀ (y : Y) (k : K),
      ‖canonicalJacquetFamily a hφ (deform z t) (torus y * k.val)‖ ≤
        A * Real.exp (torusModularLog (r + 1) y / 2 + (r : ℝ) * δ * ∑ i, |y i|) := by
  obtain ⟨C, hC⟩ := (isCompact_range hφ.1).isBounded.exists_norm_le
  have hφC (k : U) : ‖φ k‖ ≤ max C 0 := (hC _ (mem_range_self _)).trans (le_max_left _ _)
  let z0 := deform z (δ : ℂ)
  let f0 := standardSection z0 (1 : U → ℂ)
  have hd0 : z0 ∈ realSpectralChamber r := deform_mem_chamber z hz (by simpa using hδ)
  have hI0 := integrable_additiveJacquetKernel_of_mem_principalSeries a
    (RealStrictCharacterLanglandsQuotient.isSignedPower (characterList (0 : L) z0))
    (isStrictlyDominant_characterList (0 : L) hd0) (standardSection_mem constant_profile z0).1.1 (1 : G)
  let B (u : N) : ℝ := ‖f0 (w * u.val)‖
  have hB : Integrable B (upperStepHaar r a) := by
    simpa only [B, f0, additiveJacquetKernel, mul_one, norm_mul, norm_standardCharacter] using hI0.norm
  let J := ∫ u, B u ∂upperStepHaar r a
  have hJ : 0 ≤ J := integral_nonneg fun _ => norm_nonneg _
  refine ⟨max C 0 * J, mul_nonneg (le_max_right _ _) hJ, fun t ht y k => ?_⟩
  rw [canonicalJacquetFamily_agrees a hφ (deform_mem_chamber z hz (ht.symm ▸ hδ))]
  let c := torusModularLog (r + 1) y
  let S := ∑ i, |y i|
  let f := standardSection (deform z t) φ
  let Q := Real.exp (-c / 2 + (r : ℝ) * δ * S) * max C 0
  have hkernel (u : N) : ‖additiveJacquetKernel a f (torus y * k.val) u‖ ≤
      Q * B (conjTorus (-y) u) := by
    rw [additiveJacquetKernel, norm_mul, norm_standardCharacter, mul_one, torus_weyl_conj,
      section_norm_torus_mul hφ, rev_log]
    have hNorm := section_norm_le_reference φ hφC (deform z t) z0 (by
      intro i
      rw [deform_re z hz, show z0 = deform z (δ : ℂ) from rfl, deform_re z hz, Complex.ofReal_re, ht])
      (w * (conjTorus (-y) u).val) k
    have hEx := sum_exponent_le z hz (ht.symm ▸ hδ.le) (fun i => y i.rev)
    rw [ht, sum_abs_rev] at hEx
    change _ ≤ (Real.exp (-c / 2 + (r : ℝ) * δ * S) * max C 0) *
      ‖standardSection z0 1 (w * (conjTorus (-y) u).val)‖
    rw [mul_assoc (Real.exp _) (max C 0)]
    apply mul_le_mul _ hNorm (norm_nonneg _) (Real.exp_pos _).le
    exact Real.exp_le_exp.mpr (add_le_add le_rfl hEx)
  have hABm : AEStronglyMeasurable B ((upperStepHaar r a).map (conjTorus (-y))) := by
    have := upperStepHaar_isHaar r a
    rw [map_conjTorus]
    exact hB.aestronglyMeasurable.smul_measure _
  have hBInt : Integrable (fun u => B (conjTorus (-y) u)) (upperStepHaar r a) := by
    apply (integrable_map_measure hABm (continuous_conjTorus_right (-y)).measurable.aemeasurable).1
    have := upperStepHaar_isHaar r a
    rw [map_conjTorus]
    exact hB.smul_measure (by simp)
  have hkerInt : Integrable (additiveJacquetKernel a f (torus y * k.val)) (upperStepHaar r a) :=
    integrable_additiveJacquetKernel_of_mem_principalSeries a
      (RealStrictCharacterLanglandsQuotient.isSignedPower (characterList p (deform z t)))
      (isStrictlyDominant_characterList p (deform_mem_chamber z hz (ht.symm ▸ hδ)))
      (standardSection_mem hφ _).1.1 _
  calc
    _ ≤ ∫ u, ‖additiveJacquetKernel a f (torus y * k.val) u‖ ∂upperStepHaar r a := norm_integral_le_integral_norm _
    _ ≤ ∫ u, Q * B (conjTorus (-y) u) ∂upperStepHaar r a :=
      integral_mono hkerInt.norm (hBInt.const_mul Q) hkernel
    _ = _ := by
      rw [integral_const_mul, integral_norm_comp_conj a y hB]
      change (Real.exp (-c / 2 + (r : ℝ) * δ * S) * max C 0) * (Real.exp c * J) =
        (max C 0 * J) * Real.exp (c / 2 + (r : ℝ) * δ * S)
      rw [mul_mul_mul_comm, ← Real.exp_add, mul_comm]
      ring_nf

private theorem neg_half_modulus_le (y : Y) :
    -torusModularLog (r + 1) y / 2 ≤ (r : ℝ) * ∑ i, |y i| := by
  rw [torusModularLog_apply, ← Finset.sum_neg_distrib, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hi : (i.val : ℝ) ≤ r := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hi₀ : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have h : |(-((r + 1 : ℕ) : ℝ) + 1 + 2 * i.val) / 2| ≤ r :=
    abs_le.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
  calc
    _ = (-((r + 1 : ℕ) : ℝ) + 1 + 2 * i.val) / 2 * y i := by ring
    _ ≤ |(-((r + 1 : ℕ) : ℝ) + 1 + 2 * i.val) / 2| * |y i| := by
      rw [← abs_mul]
      exact le_abs_self _
    _ ≤ _ := mul_le_mul_of_nonneg_right h (abs_nonneg _)

/-- A continued Jacquet coefficient with uniform half-modulus estimates on nearby
vertical segments has the tempered estimate at the center of the parameter disk. -/
theorem canonicalTemperedBound_of_rightBoundary (a : ℝˣ) {p : L} {φ : U → ℂ}
    (hφ : IsCompactProfile p φ) (q : ℂ → P) (hq : Differentiable ℂ q) {D : ℝ} (hD : 0 ≤ D)
    (hBoundary : ∀ δ ∈ Ioo (0 : ℝ) 1, ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℂ, t.re = δ → |t.im| ≤ 1 →
      ∀ (y : Y) (k : K), ‖canonicalJacquetFamily a hφ (q t) (torus y * k.val)‖ ≤
        A * Real.exp (torusModularLog (r + 1) y / 2 + D * δ * ∑ i, |y i|))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : Y) (k : K),
      ‖canonicalJacquetFamily a hφ (q 0) (torus y * k.val)‖ ≤
        C * Real.exp (torusModularLog (r + 1) y / 2 + ε * ∑ i, |y i|) := by
  let W := canonicalJacquetFamily a hφ
  let E := q '' closedBall (0 : ℂ) 2
  have hE : IsCompact E := (isCompact_closedBall _ _).image hq.continuous
  have hW := canonicalJacquetFamily_properties a hφ
  obtain ⟨N₀, hN⟩ := exists_uniform_derivativeGrowth hW.2.1 hE (subset_univ E)
  obtain ⟨C, hC, hCbound⟩ := hN []
  let S (x : Y × K) : ℝ := ∑ i, |x.1 i|
  let m (y : Y) : ℝ := torusModularLog (r + 1) y / 2
  let F (t : ℂ) (x : Y × K) : ℂ :=
    (Real.exp (-m x.1) : ℂ) * W (q t) (torus x.1 * x.2.val)
  have hF (x : Y × K) : Differentiable ℂ (fun t => F t x) :=
    ((hW.2.2.1 [] _).comp hq).const_mul _
  have hS (x : Y × K) : 0 ≤ S x := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hNorm (t : ℂ) (x : Y × K) :
      ‖F t x‖ = Real.exp (-m x.1) * ‖W (q t) (torus x.1 * x.2.val)‖ := by
    change ‖(Real.exp (-m x.1) : ℂ) * W (q t) (torus x.1 * x.2.val)‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  let C₀ := C * (2 * ((r : ℝ) + 1) ^ 2) ^ N₀
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  let M := ((2 * N₀ : ℕ) : ℝ) + r
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hDisk (t : ℂ) (ht : t ∈ closedBall (0 : ℂ) 2) (x : Y × K) :
      ‖F t x‖ ≤ C₀ * Real.exp (M * S x) := by
    have htE : q t ∈ E := mem_image_of_mem _ ht
    have h := hCbound (q t) htE (torus x.1 * x.2.val)
    have hh := RealWhittakerGauge.realMatrixHeight_torus_mul_pow_le x.1 x.2 N₀
    rw [hNorm]
    calc
      _ ≤ Real.exp (-m x.1) * (C * realMatrixHeight (torus x.1 * x.2.val) ^ N₀) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ ≤ Real.exp (-m x.1) * (C₀ * Real.exp (((2 * N₀ : ℕ) : ℝ) * S x)) := by
        dsimp [C₀, S]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh hC) (Real.exp_pos _).le
      _ = C₀ * Real.exp (-m x.1 + ((2 * N₀ : ℕ) : ℝ) * S x) := by
        rw [Real.exp_add]
        ring
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC₀
        have hmod : -m x.1 ≤ (r : ℝ) * S x := by
          dsimp [m, S]
          rw [← neg_div]
          exact neg_half_modulus_le x.1
        dsimp [M]
        calc
          _ ≤ (r : ℝ) * S x + ((2 * N₀ : ℕ) : ℝ) * S x := add_le_add hmod le_rfl
          _ = _ := by ring
  have hLine (δ : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1) :
      ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℂ, t.re = δ → |t.im| ≤ 1 → ∀ x : Y × K,
        ‖F t x‖ ≤ A * Real.exp (D * δ * S x) := by
    obtain ⟨A, hA, h⟩ := hBoundary δ hδ
    refine ⟨A, hA, fun t ht hi x => ?_⟩
    rw [hNorm]
    calc
      _ ≤ Real.exp (-m x.1) * (A * Real.exp (m x.1 + D * δ * S x)) :=
        mul_le_mul_of_nonneg_left (h t ht hi x.1 x.2) (Real.exp_pos _).le
      _ = _ := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
  obtain ⟨B, hB, h⟩ := smallExponentialAtZero_of_rightBoundary hS hF hC₀ hM
    hD hDisk hLine ε hε
  refine ⟨B, hB, fun y k => ?_⟩
  have hb := h (y, k)
  rw [hNorm] at hb
  have hh := mul_le_mul_of_nonneg_left hb (Real.exp_pos (m y)).le
  change Real.exp (m y) * (Real.exp (-m y) * ‖W (q 0) (torus y * k.val)‖) ≤
    Real.exp (m y) * (B * Real.exp (ε * S (y, k))) at hh
  rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul,
    mul_left_comm, ← Real.exp_add] at hh
  exact hh

private theorem canonical_tempered_character_bound (a : ℝˣ) {p : L} {φ : U → ℂ}
    (hφ : IsCompactProfile p φ) (z : P) (hz : ∀ i, (z i).re = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : Y) (k : K),
      ‖canonicalJacquetFamily a hφ z (torus y * k.val)‖ ≤
        C * Real.exp (torusModularLog (r + 1) y / 2 + ε * ∑ i, |y i|) := by
  have hzero : deform z 0 = z := by ext i; simp [deform]
  rw [← hzero]
  refine canonicalTemperedBound_of_rightBoundary a hφ (deform z) (differentiable_deform z)
    (Nat.cast_nonneg r) (fun δ hδ => ?_) ε hε
  obtain ⟨A, hA, hb⟩ := canonical_bound_dominant_line a hφ z hz hδ.1
  exact ⟨A, hA, fun t ht _ => hb t ht⟩

/-- Every exact Whittaker coefficient of a real character list with imaginary exponents
satisfies the tempered half-modulus estimate. -/
theorem realTemperedWhittakerBound_characterList {ds : List RealBlock}
    (hds : RealJacquet.IsRealCharacterList ds) (hr : realRank ds = r + 1)
    (him : ∀ d ∈ ds, realBlockExponent d = 0) (a : ℝˣ) {W : G → ℂ}
    (hW : W ∈ realWhittakerModel r ds a) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : Y) (k : K),
      ‖W (torus y * k.val)‖ ≤ C * Real.exp (torusModularLog (r + 1) y / 2 + ε * ∑ i, |y i|) := by
  obtain ⟨cs, rfl⟩ := hds
  obtain ⟨p, z, he⟩ := RealPrincipalSeries.exists_characterList_of_map_character cs hr
  have hz (i : Fin (r + 1)) : (z i).re = 0 := by
    have hm : RealBlock.character (RealJacquetFrobenius.charData (p i) (z i)) ∈ cs.map RealBlock.character := by
      rw [he, characterList]
      exact List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩
    exact him _ hm
  have hm := (realWhittakerModels_eq r (cs.map RealBlock.character) hr a) ▸ hW
  rw [he] at hm
  obtain ⟨f, rfl⟩ := RealUniformCanonicalRange.realUniformCanonicalRangePremise r (-a) p z
    (by simpa only [neg_neg] using hm)
  exact canonical_tempered_character_bound (-a) (isCompactProfile_compactRestriction f.property) z hz ε hε

private theorem exponent_zero_expand_of_weight_zero (ds : List RealBlock)
    (hwt : ∀ d : ComplexCharacterData, RealBlock.induced d ∈ ds → d.weight = 0)
    (him : ∀ d ∈ ds, realBlockExponent d = 0) :
    ∀ b ∈ RealPrincipalSeries.expand ds, realBlockExponent b = 0 := by
  induction ds with
  | nil => simp [RealPrincipalSeries.expand]
  | cons d ds ih =>
    have hTail := ih (fun b hb => hwt b (List.mem_cons_of_mem _ hb))
      (fun b hb => him b (List.mem_cons_of_mem _ hb))
    have hHead := him d List.mem_cons_self
    intro b hb
    have he : RealPrincipalSeries.expand (d :: ds) =
        RealPrincipalSeries.expand [d] ++ RealPrincipalSeries.expand ds := by
      simp only [RealPrincipalSeries.expand, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [he, List.mem_append] at hb
    rcases hb with hb | hb
    · cases d with
      | character c =>
        change b ∈ [RealBlock.character c] at hb
        rw [List.mem_singleton] at hb
        simpa only [hb] using hHead
      | induced c =>
        have hc := hwt c List.mem_cons_self
        change b ∈
          [RealBlock.character (RealJacquetFrobenius.charData
              (RealGammaReflection.positionParity c.weight.natAbs)
              (c.exponent + (c.weight.natAbs : ℂ) / 2)),
            RealBlock.character (RealJacquetFrobenius.charData 0
              (c.exponent - (c.weight.natAbs : ℂ) / 2))] at hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl <;>
          simpa [realBlockExponent, RealJacquetFrobenius.charData, hc] using hHead
    · exact hTail b hb

/-- The scalar tempered estimate for lists of characters and weight-zero induced blocks. -/
def RealTemperedWhittakerCharacterBoundStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 →
    (∀ d : ComplexCharacterData, RealBlock.induced d ∈ ds → d.weight = 0) →
    (∀ d ∈ ds, realBlockExponent d = 0) →
    ∀ (a : ℝˣ) (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ),
      W ∈ realWhittakerModel r ds a → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
        ∀ (y : Fin (r + 1) → ℝ) (k : unitaryCompact ℝ (r + 1)),
          ‖W (torus y * k.val)‖ ≤
            C * Real.exp (torusModularLog (r + 1) y / 2 + ε * ∑ j, |y j|)

theorem realTemperedWhittakerCharacterBound : RealTemperedWhittakerCharacterBoundStatement := by
  intro r ds hr hwt him a W hW ε hε
  have hd := (RealPrincipalSeries.realRank_ascendingExpand ds).trans hr
  have hExp : ∀ b ∈ RealPrincipalSeries.ascendingExpand ds, realBlockExponent b = 0 :=
    fun b hb => exponent_zero_expand_of_weight_zero ds hwt him b
      ((RealPrincipalSeries.ascendingExpand_perm ds).mem_iff.mp hb)
  have hModel : W ∈ realWhittakerModel r (RealPrincipalSeries.ascendingExpand ds) a := by
    rw [realWhittakerModels_eq r _ hd a]
    apply RealPrincipalSeries.uniformModel_le_ascendingExpand r ds hr a
    rwa [← realWhittakerModels_eq r ds hr a]
  exact realTemperedWhittakerBound_characterList ⟨_, rfl⟩ hd hExp a hModel ε hε

end Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker
