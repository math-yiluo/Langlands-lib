import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SphericalBounds

/-! # Lemma II.4.1: the measure of the level sets `Ū(n)`

Waldspurger 2003, Lemma II.4.1: for `P = M U` standard and
`Ū(n) = {ū ∈ Ū ; δ_0(m_0(ū)) = q^{-n}}` there are `c` and `d` with
`mes(Ū(n)) ≤ c q^{n/2} n^d` for all `n ≥ 1`. The proof combines the formula (2) for `Ξ` on
`A_M`, the inequality (1) for `δ_0(m_0(a^{-1} ū a))`, and the upper bound of Lemma II.1.1
into the estimate (3), and then evaluates (3) at the powers of one element `a` with
`γ(a) < 1`. This module proves both steps for abstract data, with (1), (2) and II.1.1 as
explicit hypotheses. The conclusion is `LevelSetMeasureBound` of `SphericalBounds`.
-/

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory

namespace Langlands.HarishChandraSchwartz

universe u

section Powers

variable {X : Type*} [MeasurableSpace X]

/-- The second step of the proof of Lemma II.4.1: if for some `θ ∈ (0, 1)`, `r > 0`,
`s ≥ 0`, `d ≥ 0` and `C₃`
`∫ (1 + θ^{r m} w(u)^{-1})^{-1} w(u) dν(u) ≤ C₃ (1 + m s)^d` for all `m ∈ ℕ`
(inequality (3) at the powers `a^m`, with `θ = γ(a)` and `s = σ(a)`), and
`w = q^{-N/2}` with `q > 1` and `N` measurable, then `ν{N = n} ≤ C q^{n/2} n^d` for all
`n ≥ 1`. -/
theorem levelSetMeasureBound_of_powers {ν : Measure X} {N : X → ℤ} {w : X → ℝ}
    {q θ r s C₃ d : ℝ} (hq : 1 < q) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr : 0 < r) (hs : 0 ≤ s)
    (hd : 0 ≤ d) (hN : Measurable N) (hw : ∀ x, w x = q ^ (-(N x : ℝ) / 2))
    (h3 : ∀ m : ℕ, ∫⁻ x, ENNReal.ofReal ((1 + θ ^ (r * m) * (w x)⁻¹)⁻¹ * w x) ∂ν ≤
      ENNReal.ofReal (C₃ * (1 + m * s) ^ d)) :
    ∃ C d' : ℝ, ∀ n : ℕ, 1 ≤ n →
      ν {x | N x = n} ≤ ENNReal.ofReal (C * q ^ ((n : ℝ) / 2) * (n : ℝ) ^ d') := by
  have hq0 : 0 < q := by linarith
  have hlq : 0 < Real.log q := Real.log_pos hq
  have hlθ : Real.log θ < 0 := Real.log_neg hθ0 hθ1
  set L : ℝ := Real.log q / (2 * r * -Real.log θ) with hL_def
  have hL : 0 ≤ L := div_nonneg hlq.le (by nlinarith)
  set c : ℝ := L + 1
  set C₃' := max C₃ 0
  refine ⟨2 * C₃' * (1 + c * s) ^ d, d, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set m : ℕ := ⌈(n : ℝ) * L⌉₊ with hm_def
  have hm1 : (n : ℝ) * L ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) < n * L + 1 := Nat.ceil_lt_add_one (by positivity)
  -- `θ^{r m} ≤ q^{-n/2}`
  have hθq : θ ^ (r * m) ≤ q ^ (-(n : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos hθ0, Real.rpow_def_of_pos hq0]
    refine Real.exp_le_exp.mpr ?_
    have h1 : Real.log θ * (r * m) ≤ Real.log θ * (r * ((n : ℝ) * L)) :=
      mul_le_mul_of_nonpos_left (mul_le_mul_of_nonneg_left hm1 hr.le) hlθ.le
    have h2 : Real.log θ * (r * ((n : ℝ) * L)) = Real.log q * (-(n : ℝ) / 2) := by
      have hθne : Real.log θ ≠ 0 := hlθ.ne
      have hrne : r ≠ 0 := hr.ne'
      rw [hL_def]
      field_simp
    linarith
  set ε : ℝ := 1 / 2 * q ^ (-(n : ℝ) / 2) with hε_def
  have hε : 0 < ε := by positivity
  -- the integrand is at least `ε` on `{N = n}`
  have hpt : ∀ x, {x | N x = (n : ℤ)}.indicator (fun _ => ENNReal.ofReal ε) x ≤
      ENNReal.ofReal ((1 + θ ^ (r * m) * (w x)⁻¹)⁻¹ * w x) := by
    intro x
    by_cases hx : x ∈ {x | N x = (n : ℤ)}
    · rw [Set.indicator_of_mem hx]
      refine ENNReal.ofReal_le_ofReal ?_
      have hNx : (N x : ℝ) = n := by
        simp only [Set.mem_ofPred_eq] at hx
        exact_mod_cast hx
      have hwx : w x = q ^ (-(n : ℝ) / 2) := by rw [hw, hNx]
      have hwpos : 0 < w x := by rw [hwx]; positivity
      have hle : θ ^ (r * m) * (w x)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one hwpos, hwx]
        exact hθq
      have hge : (1 : ℝ) / 2 ≤ (1 + θ ^ (r * m) * (w x)⁻¹)⁻¹ := by
        have hpos : 0 < 1 + θ ^ (r * m) * (w x)⁻¹ := by positivity
        rw [one_div, inv_le_inv₀ (by norm_num) hpos]
        linarith
      rw [hε_def, ← hwx]
      exact mul_le_mul_of_nonneg_right hge hwpos.le
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  have hmeas : MeasurableSet {x | N x = (n : ℤ)} := hN (measurableSet_singleton _)
  have hint : ENNReal.ofReal ε * ν {x | N x = (n : ℤ)} ≤
      ENNReal.ofReal (C₃' * (1 + m * s) ^ d) := by
    rw [← lintegral_indicator_const hmeas]
    refine (lintegral_mono hpt).trans ((h3 m).trans (ENNReal.ofReal_le_ofReal ?_))
    have : 0 ≤ (1 + m * s) ^ d := Real.rpow_nonneg (by positivity) _
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) this
  -- `(1 + m s)^d ≤ (1 + c s)^d n^d`
  have hms : (1 + m * s) ^ d ≤ (1 + c * s) ^ d * (n : ℝ) ^ d := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    refine Real.rpow_le_rpow (by positivity) ?_ hd
    have hmc : (m : ℝ) ≤ c * n := by
      have : (n : ℝ) * L + 1 ≤ c * n := by
        simp only [c]
        nlinarith
      linarith
    nlinarith
  have hinv : ENNReal.ofReal (2 * q ^ ((n : ℝ) / 2)) * ENNReal.ofReal ε = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), hε_def]
    have : 2 * q ^ ((n : ℝ) / 2) * (1 / 2 * q ^ (-(n : ℝ) / 2)) = 1 := by
      rw [show -(n : ℝ) / 2 = -((n : ℝ) / 2) by ring, Real.rpow_neg hq0.le]
      field_simp
    rw [this, ENNReal.ofReal_one]
  calc ν {x | N x = (n : ℤ)}
      = ENNReal.ofReal (2 * q ^ ((n : ℝ) / 2)) * (ENNReal.ofReal ε * ν {x | N x = (n : ℤ)}) := by
        rw [← mul_assoc, hinv, one_mul]
    _ ≤ ENNReal.ofReal (2 * q ^ ((n : ℝ) / 2)) * ENNReal.ofReal (C₃' * (1 + m * s) ^ d) := by
        gcongr
    _ = ENNReal.ofReal (2 * q ^ ((n : ℝ) / 2) * (C₃' * (1 + m * s) ^ d)) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (2 * C₃' * (1 + c * s) ^ d * q ^ ((n : ℝ) / 2) * (n : ℝ) ^ d) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hC : 0 ≤ C₃' := le_max_right _ _
        calc 2 * q ^ ((n : ℝ) / 2) * (C₃' * (1 + m * s) ^ d)
            ≤ 2 * q ^ ((n : ℝ) / 2) * (C₃' * ((1 + c * s) ^ d * (n : ℝ) ^ d)) := by
              gcongr
          _ = 2 * C₃' * (1 + c * s) ^ d * q ^ ((n : ℝ) / 2) * (n : ℝ) ^ d := by ring

end Powers

section Formula

variable {G : Type u} [Group G] [MeasurableSpace G] {M U : Subgroup G}

/-- Formula (2) of the proof of Lemma II.4.1, for abstract data: for `a ∈ T`,
`Ξ(a) = γ^{-1} e(a) ∫_U w(c_a(u)) w(u) dν(u)`, where `c_a` is a map `U → U`. For
Waldspurger's data `T = A_M ∩ Ā⁺_0`, `γ = γ(G|M)`, `e = δ_0^{1/2}`,
`w(ū) = δ_0(m_0(ū))^{1/2}` and `c_a(ū) = a^{-1} ū a`. -/
def TorusXiFormula (ν : Measure U) (Ξ : G → ℝ) (T : Set M) (γ : ℝ) (e : G → ℝ)
    (w : U → ℝ) (c : M → U → U) : Prop :=
  ∀ a ∈ T, ENNReal.ofReal (Ξ a) =
    ENNReal.ofReal (γ⁻¹ * e a) * ∫⁻ u, ENNReal.ofReal (w (c a u) * w u) ∂ν

/-- The first step of the proof of Lemma II.4.1 (inequality (3)): formula (2), inequality
(1) `w(c_a(u))^{-1} ≤ C₁ (1 + g(a)^r w(u)^{-1})` and the upper bound of Lemma II.1.1 on `T`
give `∫ (1 + g(a)^r w(u)^{-1})^{-1} w(u) dν(u) ≤ C₃ (1 + σ(a))^d` for `a ∈ T`. -/
theorem averages_le_of_torusXiFormula {ν : Measure U} {Ξ σ : G → ℝ} {T : Set M} {γ : ℝ}
    {e : G → ℝ} {w : U → ℝ} {c : M → U → U} {g : M → ℝ} {r : ℝ}
    (h2 : TorusXiFormula ν Ξ T γ e w c) (hγ : 0 < γ) (he : ∀ a ∈ T, 0 < e a)
    (hw : ∀ u, 0 < w u) (hg : ∀ a ∈ T, 0 ≤ g a)
    (h1 : ∃ C₁ : ℝ, ∀ a ∈ T, ∀ u, (w (c a u))⁻¹ ≤ C₁ * (1 + g a ^ r * (w u)⁻¹))
    (hup : XiUpperBound Ξ σ ((↑) '' T) e) :
    ∃ C₃ d : ℝ, ∀ a ∈ T, ∫⁻ u, ENNReal.ofReal ((1 + g a ^ r * (w u)⁻¹)⁻¹ * w u) ∂ν ≤
      ENNReal.ofReal (C₃ * (1 + σ a) ^ d) := by
  obtain ⟨C₁, h1⟩ := h1
  obtain ⟨C, d, hup⟩ := hup
  set C₁' := max C₁ 1
  have hC₁' : 0 < C₁' := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨C₁' * γ * C, d, fun a ha => ?_⟩
  have hea := he a ha
  -- pointwise: `(1 + g^r / w)^{-1} w ≤ C₁' w(c_a u) w`
  have hpt : ∀ u, (1 + g a ^ r * (w u)⁻¹)⁻¹ * w u ≤ C₁' * (w (c a u) * w u) := by
    intro u
    have hwu := hw u
    have hwc := hw (c a u)
    have hpos : 0 < 1 + g a ^ r * (w u)⁻¹ := by
      have := Real.rpow_nonneg (hg a ha) r
      positivity
    have h := (h1 a ha u).trans (mul_le_mul_of_nonneg_right (le_max_left C₁ 1) hpos.le)
    -- `(w(c u))⁻¹ ≤ C₁' (1 + …)` gives `(1 + …)⁻¹ ≤ C₁' w(c u)`
    have h' : (1 + g a ^ r * (w u)⁻¹)⁻¹ ≤ C₁' * w (c a u) := by
      rw [inv_le_iff_one_le_mul₀ hpos]
      have := mul_le_mul_of_nonneg_left h hwc.le
      rw [mul_inv_cancel₀ hwc.ne'] at this
      linarith
    calc (1 + g a ^ r * (w u)⁻¹)⁻¹ * w u ≤ C₁' * w (c a u) * w u :=
          mul_le_mul_of_nonneg_right h' hwu.le
      _ = C₁' * (w (c a u) * w u) := by ring
  have hI : ∫⁻ u, ENNReal.ofReal (w (c a u) * w u) ∂ν =
      ENNReal.ofReal (γ * (e a)⁻¹) * ENNReal.ofReal (Ξ a) := by
    rw [h2 a ha, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    rw [show γ * (e a)⁻¹ * (γ⁻¹ * e a) = 1 by field_simp, ENNReal.ofReal_one, one_mul]
  have hΞa : Ξ a ≤ C * e a * (1 + σ a) ^ d := hup _ ⟨a, ha, rfl⟩
  calc ∫⁻ u, ENNReal.ofReal ((1 + g a ^ r * (w u)⁻¹)⁻¹ * w u) ∂ν
      ≤ ∫⁻ u, ENNReal.ofReal C₁' * ENNReal.ofReal (w (c a u) * w u) ∂ν := by
        refine lintegral_mono fun u => ?_
        rw [← ENNReal.ofReal_mul hC₁'.le]
        exact ENNReal.ofReal_le_ofReal (hpt u)
    _ = ENNReal.ofReal C₁' * (ENNReal.ofReal (γ * (e a)⁻¹) * ENNReal.ofReal (Ξ a)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hI]
    _ ≤ ENNReal.ofReal C₁' * (ENNReal.ofReal (γ * (e a)⁻¹) *
          ENNReal.ofReal (C * e a * (1 + σ a) ^ d)) := by
        gcongr
    _ = ENNReal.ofReal (C₁' * (γ * (e a)⁻¹ * (C * e a * (1 + σ a) ^ d))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC₁'.le]
    _ = ENNReal.ofReal (C₁' * γ * C * (1 + σ a) ^ d) := by
        congr 1
        field_simp

/-- Waldspurger, Lemma II.4.1, for abstract data: under formula (2), inequality (1) and the
upper bound of Lemma II.1.1 on `T`, if `T` contains the powers `a^m` of one `a` with
`0 < g(a) < 1`, `g(a^m) = g(a)^m` and `σ(a^m) ≤ m σ(a)`, and `w = q^{-N/2}` with `q > 1`
and `N` measurable, then `LevelSetMeasureBound ν N q`. For Waldspurger's data `g = γ`, with
`γ(a) = sup_{α ∈ Δ(P)} |α(a)|_F`. -/
theorem levelSetMeasureBound_of_torusXiFormula {ν : Measure U} {Ξ σ : G → ℝ} {T : Set M}
    {γ : ℝ} {e : G → ℝ} {w : U → ℝ} {c : M → U → U} {g : M → ℝ} {r : ℝ} {N : U → ℤ}
    {q : ℝ} (h2 : TorusXiFormula ν Ξ T γ e w c) (hγ : 0 < γ) (he : ∀ a ∈ T, 0 < e a)
    (hw : ∀ u, w u = q ^ (-(N u : ℝ) / 2)) (hg : ∀ a ∈ T, 0 ≤ g a) (hσ : ∀ x, 0 ≤ σ x)
    (hr : 0 < r)
    (h1 : ∃ C₁ : ℝ, ∀ a ∈ T, ∀ u, (w (c a u))⁻¹ ≤ C₁ * (1 + g a ^ r * (w u)⁻¹))
    (hup : XiUpperBound Ξ σ ((↑) '' T) e) (hq : 1 < q) (hN : Measurable N) {a₀ : M}
    (hpow : ∀ m : ℕ, a₀ ^ m ∈ T) (hga : 0 < g a₀ ∧ g a₀ < 1)
    (hgpow : ∀ m : ℕ, g (a₀ ^ m) = g a₀ ^ m)
    (hσpow : ∀ m : ℕ, σ ((a₀ ^ m : M) : G) ≤ m * σ a₀) :
    LevelSetMeasureBound ν N q := by
  have hwpos : ∀ u, 0 < w u := fun u => by rw [hw]; exact Real.rpow_pos_of_pos (by linarith) _
  obtain ⟨C₃, d, h3⟩ := averages_le_of_torusXiFormula h2 hγ he hwpos hg h1 hup
  set d' := max d 0
  have h3' : ∀ m : ℕ, ∫⁻ u, ENNReal.ofReal ((1 + g a₀ ^ (r * m) * (w u)⁻¹)⁻¹ * w u) ∂ν ≤
      ENNReal.ofReal (max C₃ 0 * (1 + m * σ a₀) ^ d') := by
    intro m
    have h := h3 _ (hpow m)
    rw [hgpow m, ← Real.rpow_natCast, ← Real.rpow_mul hga.1.le, mul_comm (m : ℝ) r] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hσm := hσpow m
    have hσ0 := hσ ((a₀ ^ m : M) : G)
    have hb : 1 ≤ 1 + σ ((a₀ ^ m : M) : G) := by linarith
    calc C₃ * (1 + σ ((a₀ ^ m : M) : G)) ^ d
        ≤ max C₃ 0 * (1 + σ ((a₀ ^ m : M) : G)) ^ d :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
      _ ≤ max C₃ 0 * (1 + σ ((a₀ ^ m : M) : G)) ^ d' :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hb (le_max_left _ _)) (le_max_right _ _)
      _ ≤ max C₃ 0 * (1 + m * σ a₀) ^ d' :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by linarith) (by linarith) (le_max_right _ _))
            (le_max_right _ _)
  exact levelSetMeasureBound_of_powers hq hga.1 hga.2 hr (hσ _) (le_max_right _ _) hN hw h3'

end Formula

end Langlands.HarishChandraSchwartz
