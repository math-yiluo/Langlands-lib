import Langlands.Global.RankinSelberg.UnequalAnalyticHeights

/-! # Decay of cusp forms with unbounded determinant

Three estimates for a vector `f` of a cuspidal operator realization of `GL_n`, all derived from
the Library's Siegel decomposition, its polynomial growth bound and its block decay. Each is
first proved for an arbitrary real function `w` on `GL_n(𝔸)` with the relevant bounds and then
specialized to `w = ‖f‖`:

* `hasChamberDecay` (from `hasChamberDecay_of_bounds`): on torus translates `torInf x * q` of a
  compact set, with `x` in a chamber but of arbitrary sum, `f` decays faster than
  `exp (-c ∑ |x i - mean x|)` for every `c`, up to a growth `exp (A |∑ x|)` whose rate `A` does
  not depend on `c`;
* `exists_norm_le_of_basis_column_row` (from `le_of_basis_column_row_of_hasChamberDecay`): if
  some column and some row of `g` are standard basis vectors, then
  `|f g| ≤ C exp (-N |log |det g||)` for every `N`;
* `exists_weighted_cover` (from `exists_weighted_cover_of_hasChamberDecay`): one measurable set
  meeting every rational orbit on which `|f| exp (-B |log |det||)` has finite integral, for every
  large `B` and every left-invariant measure finite on compact sets. -/

noncomputable section
universe u
set_option autoImplicit false

open scoped NNReal ENNReal
open NumberField MeasureTheory Langlands.Global Langlands.Automorphic
  Langlands.Automorphic.CuspidalL2 Langlands.Automorphic.ContinuousRationalFunctions

namespace Langlands.Global.RankinSelbergGlobal.UnequalAnalytic

/-! ### Means of real vectors -/

/-- Subtracting the mean gives a vector of sum zero. -/
theorem sum_sub_mean {n : ℕ} (x : Fin n → ℝ) :
    ∑ i, (x i - (∑ j, x j) / n) = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne'), sub_self]

/-- The `ℓ¹` norm is at most the `ℓ¹` distance to the mean plus the absolute sum. -/
theorem sum_abs_le_sum_abs_sub_mean {n : ℕ} (x : Fin n → ℝ) :
    ∑ i, |x i| ≤ ∑ i, |x i - (∑ j, x j) / n| + |∑ j, x j| := by
  have h1 : ∀ i, |x i| ≤ |x i - (∑ j, x j) / n| + |(∑ j, x j) / n| := fun i => by
    have := abs_add_le (x i - (∑ j, x j) / n) ((∑ j, x j) / n)
    rwa [sub_add_cancel] at this
  have h2 : (n : ℝ) * |(∑ j, x j) / n| ≤ |∑ j, x j| := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [abs_div, Nat.abs_cast, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne')]
  calc ∑ i, |x i| ≤ ∑ i, (|x i - (∑ j, x j) / n| + |(∑ j, x j) / n|) :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = ∑ i, |x i - (∑ j, x j) / n| + n * |(∑ j, x j) / n| := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
    _ ≤ _ := by linarith

/-- If one coordinate is at least `-C` and one is at most `C`, the absolute sum is at most
`n` times the distance to the mean plus `C`. -/
theorem abs_sum_le_of_coordinate_bounds {n : ℕ} (x : Fin n → ℝ) {C : ℝ} {k k' : Fin n}
    (hk : -C ≤ x k) (hk' : x k' ≤ C) :
    |∑ j, x j| ≤ n * (∑ i, |x i - (∑ j, x j) / n| + C) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Fin.pos k)
  set μ := (∑ j, x j) / n with hμ
  set D := ∑ i, |x i - μ| with hD
  have hsk : |x k - μ| ≤ D :=
    Finset.single_le_sum (f := fun i => |x i - μ|) (fun i _ => abs_nonneg _) (Finset.mem_univ k)
  have hsk' : |x k' - μ| ≤ D :=
    Finset.single_le_sum (f := fun i => |x i - μ|) (fun i _ => abs_nonneg _) (Finset.mem_univ k')
  have hμle : |μ| ≤ D + C := abs_le.mpr
    ⟨by linarith [le_abs_self (x k - μ)], by linarith [neg_abs_le (x k' - μ)]⟩
  have hsum : ∑ j, x j = n * μ := by rw [hμ, mul_div_cancel₀ _ hn.ne']
  rw [hsum, abs_mul, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_left hμle hn.le

/-! ### Chamber decay with unbounded sum -/

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

/-- A real function `w` on `GL_n(𝔸)` has **chamber decay** on torus translates of `Q` by the
`K`-chamber if, for every `c ≥ 0`, it is bounded on `torInf x * q` (`x` in the chamber, `q ∈ Q`)
by `C exp (-c ∑ |x i - mean x|) exp (A |∑ x|)`, with a rate `A ≥ 0` independent of `c`. -/
def HasChamberDecay (w : AdelicGL F n → ℝ) (Q : Set (AdelicGL F n)) (K : ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ c : ℝ, 0 ≤ c → ∃ C : ℝ, ∀ x : Fin n → ℝ, Chamber K x → ∀ q ∈ Q,
    w (AdelicGL.ofInfinite F n (torInf F n x) * q) ≤
      C * Real.exp (-(c * ∑ i, |x i - (∑ j, x j) / n|)) * Real.exp (A * |∑ i, x i|)

/-- **Chamber decay from growth and block decay.** A function with polynomial growth in the
height on torus translates of `Q`, and with rapid decay across every maximal block (the shape
of the Library's `exists_torus_growth` and `exists_blockDecay`), has chamber decay. -/
theorem hasChamberDecay_of_bounds (w : AdelicGL F n → ℝ) {Q : Set (AdelicGL F n)} {K : ℝ}
    (hK : 0 ≤ K)
    (hgrowth : ∃ (d : ℕ) (C : ℝ), ∀ x, ∀ q ∈ Q,
      w (AdelicGL.ofInfinite F n (torInf F n x) * q) ≤
        C * ArchimedeanGL.matrixHeight F n (torInf F n x) ^ d)
    (hdecay : ∃ d : ℕ, ∀ {a b : ℕ} (h : a + b = n), 0 < a → 0 < b → ∀ N : ℕ, ∃ C : ℝ,
      ∀ (x : Fin n → ℝ) (ℓ : ℝ), 0 ≤ ℓ →
        (∀ p r, x (finSumFinEquiv.trans (finCongr h) (Sum.inr r)) -
          x (finSumFinEquiv.trans (finCongr h) (Sum.inl p)) ≤ -ℓ) →
        ∀ q ∈ Q, w (AdelicGL.ofInfinite F n (torInf F n x) * q) ≤
          C * Real.exp (-(N * ℓ)) * ArchimedeanGL.matrixHeight F n (torInf F n x) ^ d) :
    HasChamberDecay w Q K := by
  obtain ⟨C₀, c₀, hC₀, hc₀, hH⟩ := exists_matrixHeight_torInf_le F n
  obtain ⟨d₁, C₁, hC₁⟩ := hgrowth
  obtain ⟨d₂, hdecay⟩ := hdecay
  refine ⟨c₀ * (d₁ + d₂), by positivity, fun c hc => ?_⟩
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℝ, (n : ℝ) * (0 + n * (n * (K + 2 * n * K))) = B₀ := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ⌈(n : ℝ) ^ 3 * (c + d₂ * c₀)⌉₊ = N := ⟨_, rfl⟩
  have hblock : ∀ a : Fin n, ∃ Cb : ℝ, 0 < a.val → ∀ (x : Fin n → ℝ) (ℓ : ℝ), 0 ≤ ℓ →
      (∀ i j : Fin n, i.val < a.val → a.val ≤ j.val → x j - x i ≤ -ℓ) → ∀ q ∈ Q,
        w (AdelicGL.ofInfinite F n (torInf F n x) * q) ≤
          Cb * Real.exp (-(N * ℓ)) * ArchimedeanGL.matrixHeight F n (torInf F n x) ^ d₂ := by
    intro a
    by_cases ha : 0 < a.val
    · have h : a.val + (n - a.val) = n := Nat.add_sub_cancel' a.isLt.le
      refine (hdecay h ha (by omega) N).elim fun Cb hCb => ?_
      refine ⟨Cb, fun _ x ℓ hℓ hx q hq => hCb x ℓ hℓ (fun p r => hx _ _ ?_ ?_) q hq⟩
      · simp
      · simp
    · exact ⟨0, fun h => absurd h ha⟩
  choose Cb hCb using hblock
  have hG₁0 : 0 ≤ |C₁| * (C₀ * Real.exp (c₀ * B₀)) ^ d₁ * Real.exp (c * B₀) := by positivity
  have hG₂0 : 0 ≤ (∑ a, |Cb a|) * C₀ ^ d₂ * Real.exp ((c + d₂ * c₀) * B₀) := by positivity
  refine ⟨|C₁| * (C₀ * Real.exp (c₀ * B₀)) ^ d₁ * Real.exp (c * B₀) +
    (∑ a, |Cb a|) * C₀ ^ d₂ * Real.exp ((c + d₂ * c₀) * B₀), fun x hx q hq => ?_⟩
  obtain ⟨x', hx'⟩ : ∃ x' : Fin n → ℝ, (fun i => x i - (∑ j, x j) / n) = x' := ⟨_, rfl⟩
  have hsum' : ∑ i, x' i = 0 := by rw [← hx']; exact sum_sub_mean x
  have hdiff : ∀ i j, x' j - x' i = x j - x i := fun i j => by rw [← hx']; ring
  have hx'c : Chamber K x' := fun i j hij => by rw [hdiff]; exact hx i j hij
  have hR : |∑ i, x' i| ≤ 0 := by rw [hsum', abs_zero]
  obtain ⟨s, hs⟩ : ∃ s : ℝ, ∑ i, |x i - (∑ j, x j) / n| = s := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, |∑ i, x i| = σ := ⟨_, rfl⟩
  have hs' : ∑ i, |x' i| = s := by rw [← hx', hs]
  rw [hs, hσ]
  have hs0 : 0 ≤ s := hs ▸ Finset.sum_nonneg fun i _ => abs_nonneg _
  have hσ0 : 0 ≤ σ := hσ ▸ abs_nonneg _
  have hl1 : ∑ i, |x i| ≤ s + σ := by rw [← hs, ← hσ]; exact sum_abs_le_sum_abs_sub_mean x
  have hH1 : 1 ≤ ArchimedeanGL.matrixHeight F n (torInf F n x) :=
    ArchimedeanGL.one_le_matrixHeight F n _
  have hH0 : 0 ≤ ArchimedeanGL.matrixHeight F n (torInf F n x) := zero_le_one.trans hH1
  have hHx : ArchimedeanGL.matrixHeight F n (torInf F n x) ≤ C₀ * Real.exp (c₀ * (s + σ)) :=
    (hH x).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hl1 hc₀)) hC₀)
  have hexp0 : 0 < Real.exp (-(c * s)) := Real.exp_pos _
  have hAσ : ∀ d : ℕ, d ≤ d₁ + d₂ → Real.exp (d * (c₀ * σ)) ≤ Real.exp (c₀ * (d₁ + d₂) * σ) :=
    fun d hd => Real.exp_le_exp.mpr (by
      have h1 : (d : ℝ) ≤ d₁ + d₂ := by exact_mod_cast hd
      have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hc₀ hσ0)
      linarith)
  have hAσ0 : 0 < Real.exp (c₀ * (d₁ + d₂) * σ) := Real.exp_pos _
  rcases chamber_alternative hK x' hx'c hR with h1 | ⟨a, ha, ℓ, hℓ, hgap, h2⟩
  · rw [hs', hB₀] at h1
    have hHB : ArchimedeanGL.matrixHeight F n (torInf F n x) ≤
        C₀ * Real.exp (c₀ * B₀) * Real.exp (c₀ * σ) :=
      calc ArchimedeanGL.matrixHeight F n (torInf F n x) ≤ C₀ * Real.exp (c₀ * (s + σ)) := hHx
        _ ≤ C₀ * Real.exp (c₀ * (B₀ + σ)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
              (mul_le_mul_of_nonneg_left (by linarith) hc₀)) hC₀
        _ = C₀ * Real.exp (c₀ * B₀) * Real.exp (c₀ * σ) := by
            rw [mul_add, Real.exp_add, mul_assoc]
    have hlow : 1 ≤ Real.exp (c * B₀) * Real.exp (-(c * s)) := by
      rw [← Real.exp_add]
      have hcB := mul_le_mul_of_nonneg_left h1 hc
      exact Real.one_le_exp (by linarith)
    have hpow : ArchimedeanGL.matrixHeight F n (torInf F n x) ^ d₁ ≤
        (C₀ * Real.exp (c₀ * B₀)) ^ d₁ * Real.exp (d₁ * (c₀ * σ)) := by
      rw [Real.exp_nat_mul, ← mul_pow]
      exact pow_le_pow_left₀ hH0 hHB d₁
    have hC₀B : 0 ≤ (C₀ * Real.exp (c₀ * B₀)) ^ d₁ := by positivity
    calc _ ≤ C₁ * ArchimedeanGL.matrixHeight F n (torInf F n x) ^ d₁ := hC₁ x q hq
      _ ≤ |C₁| * ArchimedeanGL.matrixHeight F n (torInf F n x) ^ d₁ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 _)
      _ ≤ |C₁| * ((C₀ * Real.exp (c₀ * B₀)) ^ d₁ * Real.exp (d₁ * (c₀ * σ))) :=
          mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
      _ ≤ |C₁| * ((C₀ * Real.exp (c₀ * B₀)) ^ d₁ *
            Real.exp (c₀ * (d₁ + d₂) * σ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hAσ d₁ (by omega)) hC₀B)
            (abs_nonneg _)
      _ ≤ |C₁| * ((C₀ * Real.exp (c₀ * B₀)) ^ d₁ * Real.exp (c₀ * (d₁ + d₂) * σ)) *
            (Real.exp (c * B₀) * Real.exp (-(c * s))) :=
          le_mul_of_one_le_right (by positivity) hlow
      _ = |C₁| * (C₀ * Real.exp (c₀ * B₀)) ^ d₁ * Real.exp (c * B₀) * Real.exp (-(c * s)) *
            Real.exp (c₀ * (d₁ + d₂) * σ) := by ring
      _ ≤ (|C₁| * (C₀ * Real.exp (c₀ * B₀)) ^ d₁ * Real.exp (c * B₀) +
            (∑ a, |Cb a|) * C₀ ^ d₂ * Real.exp ((c + d₂ * c₀) * B₀)) * Real.exp (-(c * s)) *
            Real.exp (c₀ * (d₁ + d₂) * σ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right hG₂0) hexp0.le) hAσ0.le
  · rw [hs'] at h2
    have hgapx : ∀ i j : Fin n, i.val < a.val → a.val ≤ j.val → x j - x i ≤ -ℓ :=
      fun i j hi hj => by rw [← hdiff]; exact hgap i j hi hj
    have hHd : ArchimedeanGL.matrixHeight F n (torInf F n x) ^ d₂ ≤
        C₀ ^ d₂ * Real.exp (d₂ * (c₀ * (s + σ))) := by
      rw [Real.exp_nat_mul, ← mul_pow]
      exact pow_le_pow_left₀ hH0 hHx d₂
    have hkey : -(N * ℓ) + d₂ * (c₀ * s) ≤ (c + d₂ * c₀) * B₀ + -(c * s) := by
      have hNc : (n : ℝ) ^ 3 * (c + d₂ * c₀) ≤ N := hN ▸ Nat.le_ceil _
      have hcd : 0 ≤ c + d₂ * c₀ := by positivity
      have h2' : s ≤ B₀ + (n : ℝ) ^ 3 * ℓ := by rw [← hB₀]; linarith
      exact decay_exponent_le hcd hℓ h2' hNc
    have hCa : |Cb a| ≤ ∑ a, |Cb a| :=
      Finset.single_le_sum (f := fun a => |Cb a|) (fun a _ => abs_nonneg _) (Finset.mem_univ a)
    have hC₀d : 0 ≤ C₀ ^ d₂ := pow_nonneg hC₀ _
    calc _ ≤ Cb a * Real.exp (-(N * ℓ)) * ArchimedeanGL.matrixHeight F n (torInf F n x) ^ d₂ :=
          hCb a ha x ℓ hℓ hgapx q hq
      _ ≤ |Cb a| * Real.exp (-(N * ℓ)) * (C₀ ^ d₂ * Real.exp (d₂ * (c₀ * (s + σ)))) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le) hHd
            (pow_nonneg hH0 _) (by positivity)
      _ = |Cb a| * C₀ ^ d₂ * Real.exp (-(N * ℓ) + d₂ * (c₀ * s)) *
            Real.exp (d₂ * (c₀ * σ)) := by
          rw [mul_add, mul_add, Real.exp_add, Real.exp_add]; ring
      _ ≤ (∑ a, |Cb a|) * C₀ ^ d₂ * Real.exp ((c + d₂ * c₀) * B₀ + -(c * s)) *
            Real.exp (c₀ * (d₁ + d₂) * σ) :=
          mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hCa hC₀d)
            (Real.exp_le_exp.mpr hkey) (Real.exp_pos _).le (by positivity))
            (hAσ d₂ (by omega)) (Real.exp_pos _).le (by positivity)
      _ = (∑ a, |Cb a|) * C₀ ^ d₂ * Real.exp ((c + d₂ * c₀) * B₀) * Real.exp (-(c * s)) *
            Real.exp (c₀ * (d₁ + d₂) * σ) := by
          rw [Real.exp_add]; ring
      _ ≤ (|C₁| * (C₀ * Real.exp (c₀ * B₀)) ^ d₁ * Real.exp (c * B₀) +
            (∑ a, |Cb a|) * C₀ ^ d₂ * Real.exp ((c + d₂ * c₀) * B₀)) * Real.exp (-(c * s)) *
            Real.exp (c₀ * (d₁ + d₂) * σ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_left hG₁0) hexp0.le) hAσ0.le

/-! ### Decay from a basis column and a basis row -/

/-- The logarithm of the determinant of a torus translate. -/
theorem log_absDet_torInf_mul (x : Fin n → ℝ) (q : AdelicGL F n) :
    Real.log (absDet F n (AdelicGL.ofInfinite F n (torInf F n x) * q)) =
      Module.finrank ℚ F * ∑ i, x i + Real.log (absDet F n q) := by
  rw [absDet_mul, absDet_ofInfinite_torInf,
    Real.log_mul (pow_pos (Real.exp_pos _) _).ne' (absDet_pos F n q).ne', Real.log_pow,
    Real.log_exp]

/-- On a compact set, `|log |det||` is bounded. -/
theorem exists_abs_log_absDet_le {Q : Set (AdelicGL F n)} (hQ : IsCompact Q) :
    ∃ L : ℝ, ∀ q ∈ Q, |Real.log (absDet F n q)| ≤ L :=
  (hQ.image (continuous_abs.comp ((continuous_absDet F n).log
    fun g => (absDet_pos F n g).ne'))).bddAbove.elim
    fun L hL => ⟨L, fun q hq => hL ⟨q, hq, rfl⟩⟩

/-- **Decay from a basis column and a basis row, for a function with chamber decay.** If `w` is
left invariant under `GL_n(F)` and has chamber decay on every compact set and chamber, then
`w g ≤ C exp (-N |log |det g||)` whenever some column and some row of `g` are standard basis
vectors, for every `N ≥ 0`. -/
theorem le_of_basis_column_row_of_hasChamberDecay (w : AdelicGL F n → ℝ)
    (hw : ∀ (γ : RationalGL F n) (g : AdelicGL F n), w (AdelicGL.rational F n γ * g) = w g)
    (hdecay : ∀ Q : Set (AdelicGL F n), IsCompact Q → ∀ K : ℝ, 0 ≤ K → HasChamberDecay w Q K)
    (hn : 0 < n) (N : ℝ) (hN : 0 ≤ N) :
    ∃ C : ℝ, ∀ g : AdelicGL F n,
      (∃ j, ∀ i, (g : Matrix (Fin n) (Fin n) (Adeles F)) i j =
          (1 : Matrix (Fin n) (Fin n) (Adeles F)) i j) →
      (∃ i, ∀ j, (g : Matrix (Fin n) (Fin n) (Adeles F)) i j =
          (1 : Matrix (Fin n) (Fin n) (Adeles F)) i j) →
      w g ≤ C * Real.exp (-(N * |Real.log (absDet F n g)|)) := by
  obtain ⟨Q₁, K, hQ₁, hK, hdec⟩ := exists_siegelDecomposition F n
  obtain ⟨C', hC'⟩ := exists_coordinate_bounds F hn hQ₁
  obtain ⟨L, hL⟩ := exists_abs_log_absDet_le (F := F) hQ₁
  obtain ⟨A, hA, hdecay⟩ := hdecay Q₁ hQ₁ K hK
  have hd : (0 : ℝ) < (Module.finrank ℚ F : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have hAN : 0 ≤ A + N * (Module.finrank ℚ F : ℝ) := by positivity
  obtain ⟨Cc, hCc⟩ := hdecay ((A + N * (Module.finrank ℚ F : ℝ)) * n) (by positivity)
  refine ⟨|Cc| * Real.exp ((A + N * (Module.finrank ℚ F : ℝ)) * n * C' + N * L),
    fun g hcol hrow => ?_⟩
  obtain ⟨γ, x, q, hq, hγ, hx⟩ := hdec g
  obtain ⟨k, hk⟩ := (hC' g γ x q hq hγ).1 hcol
  obtain ⟨k', hk'⟩ := (hC' g γ x q hq hγ).2 hrow
  have hD := abs_sum_le_of_coordinate_bounds x hk hk'
  have hb := hCc x hx q hq
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, ∑ i, |x i - (∑ j, x j) / n| = D := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, |∑ j, x j| = σ := ⟨_, rfl⟩
  rw [hDdef, hσ] at hD hb
  have hσ0 : 0 ≤ σ := hσ ▸ abs_nonneg _
  have hlog : |Real.log (absDet F n g)| ≤ (Module.finrank ℚ F : ℝ) * σ + L := by
    rw [← absDet_rational_mul F n γ g, hγ, log_absDet_torInf_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, Nat.abs_cast, hσ]
    linarith [hL q hq]
  have hev : w g = w (AdelicGL.ofInfinite F n (torInf F n x) * q) := by
    rw [← hw γ g, hγ]
  have h1 := mul_le_mul_of_nonneg_left hD hAN
  have h2 := mul_le_mul_of_nonneg_left hlog hN
  calc w g = w (AdelicGL.ofInfinite F n (torInf F n x) * q) := hev
    _ ≤ Cc * Real.exp (-((A + N * (Module.finrank ℚ F : ℝ)) * n * D)) * Real.exp (A * σ) := hb
    _ ≤ |Cc| * Real.exp (-((A + N * (Module.finrank ℚ F : ℝ)) * n * D) + A * σ) := by
        rw [Real.exp_add, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le) (Real.exp_pos _).le
    _ ≤ |Cc| * Real.exp ((A + N * (Module.finrank ℚ F : ℝ)) * n * C' + N * L +
          -(N * |Real.log (absDet F n g)|)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
        linarith
    _ = |Cc| * Real.exp ((A + N * (Module.finrank ℚ F : ℝ)) * n * C' + N * L) *
          Real.exp (-(N * |Real.log (absDet F n g)|)) := by
        rw [Real.exp_add]; ring

/-! ### A weighted lattice cover -/

/-- Exponential decay in the `ℓ¹` norm is summable over any set of integer vectors. -/
theorem summable_lattice_bound {n : ℕ} (P : (Fin n → ℤ) → Prop) (A : ℝ) :
    Summable fun m : {m : Fin n → ℤ // P m} =>
      A * Real.exp (-(∑ i, |((m.1 i : ℤ) : ℝ)|)) := by
  have hs : Summable fun m : Fin n → ℤ => ∏ i, Real.exp (-(1 * |((m i : ℤ) : ℝ)|)) :=
    summable_prod_fin (fun k : ℤ => Real.exp (-(1 * |(k : ℝ)|)))
      (summable_exp_neg_mul_abs_int one_pos) fun k => (Real.exp_pos _).le
  refine ((hs.comp_injective Subtype.val_injective).mul_left A).congr fun m => ?_
  simp only [Function.comp_apply, one_mul]
  rw [← Real.exp_sum, Finset.sum_neg_distrib]

section Measure

variable [MeasurableSpace (AdelicGL F n)] [BorelSpace (AdelicGL F n)]

/-- **A weighted cover, for functions with chamber decay.** There is one measurable set `t`
meeting the rational orbit of every adelic matrix such that, for every function `w` with chamber
decay on every compact set and chamber, the integral of `w exp (-B |log |det||)` over `t` is
finite for all large `B`, for every left-invariant measure finite on compact sets. -/
theorem exists_weighted_cover_of_hasChamberDecay :
    ∃ t : Set (AdelicGL F n), MeasurableSet t ∧
      (∀ g : AdelicGL F n, ∃ γ : RationalGL F n, AdelicGL.rational F n γ * g ∈ t) ∧
      ∀ w : AdelicGL F n → ℝ,
        (∀ Q : Set (AdelicGL F n), IsCompact Q → ∀ K : ℝ, 0 ≤ K → HasChamberDecay w Q K) →
        ∃ B₀ : ℝ, ∀ B : ℝ, B₀ ≤ B →
          ∀ (μ : Measure (AdelicGL F n)) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ],
            (∫⁻ x in t, ENNReal.ofReal (w x) *
              ENNReal.ofReal (Real.exp (-(B * |Real.log (absDet F n x)|))) ∂μ) < ⊤ := by
  have := adelicGL_t2Space F n
  obtain ⟨Q₁, K, hQ₁, hK, hdec⟩ := exists_siegelDecomposition F n
  obtain ⟨L, hL⟩ := exists_abs_log_absDet_le (F := F) hQ₁
  obtain ⟨Q₂, hQ₂def⟩ : ∃ Q₂ : Set (AdelicGL F n), (fun p : (Fin n → ℝ) × AdelicGL F n =>
      AdelicGL.ofInfinite F n (torInf F n p.1) * p.2) ''
        ((Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1) ×ˢ Q₁) = Q₂ := ⟨_, rfl⟩
  have hQ₂ : IsCompact Q₂ := hQ₂def ▸ ((isCompact_univ_pi fun _ => isCompact_Icc).prod hQ₁).image
    (((map_continuous (AdelicGL.ofInfinite F n)).comp
      ((continuous_torInf F n).comp continuous_fst)).mul continuous_snd)
  let ι := {m : Fin n → ℤ // Chamber (K + 1) (fun i => (m i : ℝ))}
  let a : ι → AdelicGL F n := fun m => AdelicGL.ofInfinite F n (torInf F n fun i => (m.1 i : ℝ))
  refine ⟨leftTranslateCover a Q₂, measurableSet_leftTranslateCover a hQ₂, ?_, ?_⟩
  · intro g
    obtain ⟨γ, x, q, hq, hγ, hx⟩ := hdec g
    have hc := (floor_chamber x hx le_rfl).1
    have hxy : (fun i => ((⌊x i⌋ : ℤ) : ℝ)) + (fun i => Int.fract (x i)) = x :=
      funext fun i => Int.floor_add_fract (x i)
    refine ⟨γ, Set.mem_iUnion.mpr ⟨⟨fun i => ⌊x i⌋, hc⟩,
      AdelicGL.ofInfinite F n (torInf F n fun i => Int.fract (x i)) * q,
      hQ₂def ▸ ⟨(fun i => Int.fract (x i), q),
        ⟨fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, hq⟩, rfl⟩, ?_⟩⟩
    show AdelicGL.ofInfinite F n (torInf F n fun i => ((⌊x i⌋ : ℤ) : ℝ)) *
      (AdelicGL.ofInfinite F n (torInf F n fun i => Int.fract (x i)) * q) =
        AdelicGL.rational F n γ * g
    rw [hγ, ← mul_assoc, ← map_mul, ← torInf_add, hxy]
  · intro w hw
    obtain ⟨A, hA, hdecay⟩ := hw Q₁ hQ₁ (K + 2) (by linarith)
    obtain ⟨C, hC⟩ := hdecay 1 zero_le_one
    refine ⟨A + 1, fun B hB μ _ _ => ?_⟩
    have hB0 : 0 ≤ B := by linarith
    have hd : (1 : ℝ) ≤ Module.finrank ℚ F := Nat.one_le_cast.mpr Module.finrank_pos
    let b : ι → ℝ≥0∞ := fun m => ENNReal.ofReal
      (|C| * Real.exp (B * L + n) * Real.exp (-(∑ i, |((m.1 i : ℤ) : ℝ)|)))
    refine lintegral_leftTranslateCover_lt_top μ a Q₂ hQ₂.measure_lt_top _ b ?_ ?_
    · intro m z hz
      rw [← hQ₂def] at hz
      obtain ⟨p, hp, hpz⟩ := hz
      have hpz' : AdelicGL.ofInfinite F n (torInf F n p.1) * p.2 = z := hpz
      obtain ⟨hX, -, hXm⟩ := shift_chamber (R := |∑ i, ((m.1 i : ℤ) : ℝ)|)
        (fun i => ((m.1 i : ℤ) : ℝ)) p.1 (fun i => hp.1 i (Set.mem_univ i)) m.2
        (le_add_of_nonneg_right (Nat.cast_nonneg n))
      obtain ⟨X, hXdef⟩ : ∃ X : Fin n → ℝ, (fun i => ((m.1 i : ℤ) : ℝ)) + p.1 = X := ⟨_, rfl⟩
      rw [hXdef] at hX hXm
      have heq : a m * z = AdelicGL.ofInfinite F n (torInf F n X) * p.2 := by
        rw [← hpz']
        show AdelicGL.ofInfinite F n (torInf F n fun i => ((m.1 i : ℤ) : ℝ)) *
          (AdelicGL.ofInfinite F n (torInf F n p.1) * p.2) = _
        rw [← mul_assoc, ← map_mul, ← torInf_add, hXdef]
      have hq : p.2 ∈ Q₁ := hp.2
      have hb := hC X hX p.2 hq
      have hl1 := sum_abs_le_sum_abs_sub_mean X
      have hlog0 := log_absDet_torInf_mul X p.2
      obtain ⟨D, hD⟩ : ∃ D : ℝ, ∑ i, |X i - (∑ j, X j) / n| = D := ⟨_, rfl⟩
      obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, |∑ j, X j| = σ := ⟨_, rfl⟩
      obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ,
          Real.log (absDet F n (AdelicGL.ofInfinite F n (torInf F n X) * p.2)) = Λ := ⟨_, rfl⟩
      rw [hD, hσ] at hb hl1
      rw [hΛ] at hlog0
      have hσ0 : 0 ≤ σ := hσ ▸ abs_nonneg _
      have hlog : σ - L ≤ |Λ| := by
        rw [hlog0]
        have h1 : σ ≤ (Module.finrank ℚ F : ℝ) * σ := le_mul_of_one_le_left hσ0 hd
        have h2 := abs_sub_abs_le_abs_sub ((Module.finrank ℚ F : ℝ) * ∑ i, X i)
          (-Real.log (absDet F n p.2))
        rw [sub_neg_eq_add, abs_mul, Nat.abs_cast, abs_neg, hσ] at h2
        linarith [hL p.2 hq]
      show ENNReal.ofReal (w (a m * z)) *
          ENNReal.ofReal (Real.exp (-(B * |Real.log (absDet F n (a m * z))|))) ≤ b m
      rw [heq, hΛ, ← ENNReal.ofReal_mul' (Real.exp_pos _).le]
      refine ENNReal.ofReal_le_ofReal ?_
      have hw' : Real.exp (-(B * |Λ|)) ≤ Real.exp (-(B * σ) + B * L) :=
        Real.exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_left hlog hB0])
      have hb' : w (AdelicGL.ofInfinite F n (torInf F n X) * p.2) ≤
          |C| * Real.exp (-(1 * D) + A * σ) := by
        rw [Real.exp_add, ← mul_assoc]
        exact hb.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le) (Real.exp_pos _).le)
      calc _ ≤ |C| * Real.exp (-(1 * D) + A * σ) * Real.exp (-(B * σ) + B * L) :=
            mul_le_mul hb' hw' (Real.exp_pos _).le (by positivity)
        _ = |C| * Real.exp (-(1 * D) + A * σ + (-(B * σ) + B * L)) := by
            rw [Real.exp_add (-(1 * D) + A * σ)]; ring
        _ ≤ |C| * Real.exp (B * L + n + -(∑ i, |((m.1 i : ℤ) : ℝ)|)) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
            have h3 : 0 ≤ (B - A - 1) * σ := mul_nonneg (by linarith) hσ0
            linarith
        _ = _ := by rw [Real.exp_add (B * L + n)]; ring
    · have hsum := summable_lattice_bound (fun m : Fin n → ℤ => Chamber (K + 1)
        (fun i => (m i : ℝ))) (|C| * Real.exp (B * L + n))
      have hb : (∑' m, b m) = ENNReal.ofReal (∑' m : ι,
          |C| * Real.exp (B * L + n) * Real.exp (-(∑ i, |((m.1 i : ℤ) : ℝ)|))) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum).symm
      rw [hb]
      exact ENNReal.ofReal_lt_top

end Measure

/-! ### Cusp forms -/

variable (S : OperatorRealization F n)

/-- **Chamber decay with unbounded determinant.** On torus translates of a compact set by
chamber vectors `x` of arbitrary sum, a cuspidal vector decays faster than
`exp (-c ∑ |x i - mean x|)` for every `c ≥ 0`, up to the factor `exp (A |∑ x|)`, where the
rate `A` is independent of `c`. -/
theorem hasChamberDecay [CompactSpace (AdeleQuotient F)] (hS : S.IsCuspidal)
    (f : S.Space) (Q : Set (AdelicGL F n)) (hQ : IsCompact Q) {K : ℝ} (hK : 0 ≤ K) :
    HasChamberDecay (fun g => ‖evaluate F n (S.toContinuous f) g‖) Q K :=
  hasChamberDecay_of_bounds _ hK (S.exists_torus_growth f Q hQ) (S.exists_blockDecay hS f Q hQ)

/-- **Decay from a basis column and a basis row.** If some column and some row of `g` are
standard basis vectors, a cuspidal vector is bounded at `g` by `C exp (-N |log |det g||)`, for
every `N ≥ 0`. -/
theorem exists_norm_le_of_basis_column_row [CompactSpace (AdeleQuotient F)] (hS : S.IsCuspidal)
    (f : S.Space) (hn : 0 < n) (N : ℝ) (hN : 0 ≤ N) :
    ∃ C : ℝ, ∀ g : AdelicGL F n,
      (∃ j, ∀ i, (g : Matrix (Fin n) (Fin n) (Adeles F)) i j =
          (1 : Matrix (Fin n) (Fin n) (Adeles F)) i j) →
      (∃ i, ∀ j, (g : Matrix (Fin n) (Fin n) (Adeles F)) i j =
          (1 : Matrix (Fin n) (Fin n) (Adeles F)) i j) →
      ‖evaluate F n (S.toContinuous f) g‖ ≤
        C * Real.exp (-(N * |Real.log (absDet F n g)|)) :=
  le_of_basis_column_row_of_hasChamberDecay (fun g => ‖evaluate F n (S.toContinuous f) g‖)
    (fun γ g => congrArg (fun z => ‖z‖) (evaluate_rational F n (S.toContinuous f) γ g))
    (fun Q hQ _ hK => hasChamberDecay S hS f Q hQ hK) hn N hN

/-- **A weighted cover.** There is one measurable set `t` meeting the rational orbit of every
adelic matrix such that, for every cuspidal vector `f`, the weighted integral of
`|f| exp (-B |log |det||)` over `t` is finite for all large `B`, for every left-invariant
measure finite on compact sets. -/
theorem exists_weighted_cover [CompactSpace (AdeleQuotient F)] [MeasurableSpace (AdelicGL F n)]
    [BorelSpace (AdelicGL F n)] (hS : S.IsCuspidal) :
    ∃ t : Set (AdelicGL F n), MeasurableSet t ∧
      (∀ g : AdelicGL F n, ∃ γ : RationalGL F n, AdelicGL.rational F n γ * g ∈ t) ∧
      ∀ f : S.Space, ∃ B₀ : ℝ, ∀ B : ℝ, B₀ ≤ B →
        ∀ (μ : Measure (AdelicGL F n)) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ],
          (∫⁻ x in t, ‖evaluate F n (S.toContinuous f) x‖ₑ *
            ENNReal.ofReal (Real.exp (-(B * |Real.log (absDet F n x)|))) ∂μ) < ⊤ := by
  obtain ⟨t, ht, hcov, hint⟩ := exists_weighted_cover_of_hasChamberDecay (F := F) (n := n)
  refine ⟨t, ht, hcov, fun f => ?_⟩
  obtain ⟨B₀, hB₀⟩ := hint (fun g => ‖evaluate F n (S.toContinuous f) g‖)
    fun Q hQ _ hK => hasChamberDecay S hS f Q hQ hK
  refine ⟨B₀, fun B hB μ _ _ => ?_⟩
  simpa only [ofReal_norm] using hB₀ B hB μ

end Langlands.Global.RankinSelbergGlobal.UnequalAnalytic
