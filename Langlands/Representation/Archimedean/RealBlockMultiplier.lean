import Mathlib.Basic.Complex.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Recurrent multipliers on a parity class of integers

Pure algebra used in the proof of `RealCharacterPairFiltrationStatement`. There, a linear map
between principal series of `GL_2(ℝ)`, built in the block coordinates `p, p + 1`, multiplies
the `k`-th rotation Fourier coefficient by a scalar `μ k`; its compatibility with the Lie
algebra action becomes a two-term recurrence for `μ` on a parity class `k ≡ ε (mod 2)`, and
its compatibility with the sign reflections a symmetry `μ (-k) = σ μ k`. Those equivalences
are proved where the multipliers are used, not here. This module defines
both conditions (`IsRecurrent`, `IsSymmetric`) and constructs three explicit solutions with
prescribed zeros, for `ε ∈ {0, 1}`:

* `genericMultiplier ν ε`, for `δ = ν + 1` with `0 < re ν` and `ν ≠ ε + 2m + 1`: no zeros, and
  `μ (ε + 2m) = ∏_{i<m} (ε + 2i + 1 - ν) / (ε + 2i + 1 + ν)`;
* `binomialMultiplier ℓ ε`, for `δ = ℓ + 1` with `0 < ℓ` and `ℓ - 1 ≡ ε`: support `|k| < ℓ`, and
  `μ (ε + 2m) = (-1)^m C(ℓ - 1, (ε + 2m + ℓ - 1) / 2)`;
* `tailMultiplier ℓ ε σ`, for `δ = 1 - ℓ` with the same `ℓ`, symmetric for any `σ` with
  `σ² = 1`: support `|k| > ℓ`, and `P (ε + 2m) = C((ε + 2m + ℓ - 1) / 2, ℓ)`.

The first two are symmetric for `σ = (-1)^ε`. Each is the extension by symmetry (`extend`) of
a solution on the nonnegative half of the parity class. `IsRecurrent.inv`: the inverse of a
solution for `δ` without zeros solves the recurrence for `2 - δ`.
-/

noncomputable section

namespace Langlands.Archimedean.RealBlockMultiplier

open Finset

/-- The recurrence `μ (k + 2) (δ + k) = (k + 2 - δ) μ k` on the parity class `k ≡ ε (mod 2)`. -/
def IsRecurrent (δ : ℂ) (ε : ℤ) (μ : ℤ → ℂ) : Prop :=
  ∀ k : ℤ, Even (k - ε) → μ (k + 2) * (δ + k) = ((k : ℂ) + 2 - δ) * μ k

/-- The symmetry `μ (-k) = σ μ k` on the parity class `k ≡ ε (mod 2)`. -/
def IsSymmetric (ε : ℤ) (σ : ℂ) (μ : ℤ → ℂ) : Prop :=
  ∀ k : ℤ, Even (k - ε) → μ (-k) = σ * μ k

/-! ## Inverses -/

/-- The inverse of a solution of the recurrence for `δ` without zeros on the parity class solves
the recurrence for `2 - δ`. -/
theorem IsRecurrent.inv {δ : ℂ} {ε : ℤ} {μ : ℤ → ℂ} (h : IsRecurrent δ ε μ)
    (h0 : ∀ k : ℤ, Even (k - ε) → μ k ≠ 0) :
    IsRecurrent (2 - δ) ε fun k => (μ k)⁻¹ := by
  intro k hk
  have hk2 : Even (k + 2 - ε) := by
    obtain ⟨r, hr⟩ := hk
    exact ⟨r + 1, by omega⟩
  have e := h k hk
  have a0 := h0 k hk
  have a2 := h0 (k + 2) hk2
  have i0 : (μ k)⁻¹ * μ k = 1 := inv_mul_cancel₀ a0
  have i2 : (μ (k + 2))⁻¹ * μ (k + 2) = 1 := inv_mul_cancel₀ a2
  linear_combination (-(μ k)⁻¹ * (μ (k + 2))⁻¹) * e + (μ k)⁻¹ * (δ + k) * i2 -
    (μ (k + 2))⁻¹ * (k + 2 - δ) * i0

/-- The inverse of a symmetric function is symmetric for the inverse sign. -/
theorem IsSymmetric.inv {ε : ℤ} {σ : ℂ} {μ : ℤ → ℂ} (h : IsSymmetric ε σ μ) :
    IsSymmetric ε σ⁻¹ fun k => (μ k)⁻¹ := by
  intro k hk
  simp only [h k hk, mul_inv]

/-! ## Extension by symmetry -/

/-- The function on `ℤ` with value `a (|k| / 2)` at `k ≥ 0` and `σ a (|k| / 2)` at `k < 0`: on
the parity class of `ε ∈ {0, 1}` the value at `±(ε + 2m)` is determined by `a m`. -/
def extend (σ : ℂ) (a : ℕ → ℂ) (k : ℤ) : ℂ :=
  if 0 ≤ k then a (k.natAbs / 2) else σ * a (k.natAbs / 2)

theorem extend_of_nonneg {σ : ℂ} {a : ℕ → ℂ} {k : ℤ} (hk : 0 ≤ k) :
    extend σ a k = a (k.natAbs / 2) := by
  simp [extend, hk]

theorem extend_of_neg {σ : ℂ} {a : ℕ → ℂ} {k : ℤ} (hk : k < 0) :
    extend σ a k = σ * a (k.natAbs / 2) := by
  simp [extend, not_le.mpr hk]

/-- The extension of a solution of the recurrence on the nonnegative half of the parity class
is symmetric, provided the sign is compatible at the centre `k = 0` of the even class. -/
theorem isSymmetric_extend {ε : ℤ} {σ : ℂ} {a : ℕ → ℂ} (hε : ε = 0 ∨ ε = 1)
    (hσ : σ ^ 2 = 1) (hc : a 0 = 0 ∨ σ = (-1) ^ ε.natAbs) :
    IsSymmetric ε σ (extend σ a) := by
  intro k hk
  rcases lt_trichotomy k 0 with h | h | h
  · rw [extend_of_nonneg (by omega), extend_of_neg h, Int.natAbs_neg, ← mul_assoc, ← sq, hσ,
      one_mul]
  · subst h
    obtain ⟨r, hr⟩ := hk
    have hε0 : ε = 0 := by omega
    subst hε0
    simp only [neg_zero, extend_of_nonneg le_rfl, Int.natAbs_zero, Nat.zero_div]
    rcases hc with hc | hc
    · rw [hc, mul_zero]
    · rw [hc]
      simp
  · rw [extend_of_neg (by omega), extend_of_nonneg h.le, Int.natAbs_neg]

/-- The recurrence identity at `k` follows from the identity at `-k - 2` for a symmetric
function with `σ ^ 2 = 1`. -/
theorem recurrence_of_reflect {δ : ℂ} {ε : ℤ} {σ : ℂ} {μ : ℤ → ℂ} (hs : IsSymmetric ε σ μ)
    (hσ : σ ^ 2 = 1) {k : ℤ} (hk : Even (k - ε))
    (h : μ (-k - 2 + 2) * (δ + ((-k - 2 : ℤ) : ℂ)) = (((-k - 2 : ℤ) : ℂ) + 2 - δ) * μ (-k - 2)) :
    μ (k + 2) * (δ + k) = ((k : ℂ) + 2 - δ) * μ k := by
  have hk2 : Even (k + 2 - ε) := by
    obtain ⟨r, hr⟩ := hk
    exact ⟨r + 1, by omega⟩
  have e1 : μ (-k - 2 + 2) = σ * μ k := by
    rw [show -k - 2 + 2 = -k by ring, hs k hk]
  have e2 : μ (-k - 2) = σ * μ (k + 2) := by
    rw [show -k - 2 = -(k + 2) by ring, hs (k + 2) hk2]
  rw [e1, e2] at h
  push_cast at h
  linear_combination σ * h - (μ (k + 2) * (δ + k) + μ k * (δ - k - 2)) * hσ

/-- On the parity class of `ε ∈ {0, 1}`, the extension of a solution of the recurrence on the
nonnegative half is a solution, provided the sign is compatible at the centre. -/
theorem isRecurrent_extend {δ : ℂ} {ε : ℤ} {σ : ℂ} {a : ℕ → ℂ} (hε : ε = 0 ∨ ε = 1)
    (hσ : σ ^ 2 = 1) (hc : a 0 = 0 ∨ σ = (-1) ^ ε.natAbs)
    (ha : ∀ m : ℕ, a (m + 1) * (δ + ε + 2 * m) = ((ε : ℂ) + 2 * m + 2 - δ) * a m) :
    IsRecurrent δ ε (extend σ a) := by
  have hs := isSymmetric_extend hε hσ hc
  have nonneg : ∀ k : ℤ, 0 ≤ k → Even (k - ε) →
      extend σ a (k + 2) * (δ + k) = ((k : ℂ) + 2 - δ) * extend σ a k := by
    intro k h0 hk
    obtain ⟨r, hr⟩ := hk
    obtain ⟨m, hm⟩ : ∃ m : ℕ, m = k.natAbs / 2 := ⟨_, rfl⟩
    have h1 : (k + 2).natAbs / 2 = m + 1 := by omega
    have h2 : k = ε + 2 * (m : ℤ) := by omega
    have h3 : (k : ℂ) = ε + 2 * (m : ℂ) := by
      rw [h2]
      push_cast
      ring
    rw [extend_of_nonneg (by omega), extend_of_nonneg h0, h1, ← hm, h3]
    linear_combination ha m
  intro k hk
  rcases le_or_gt 0 k with h0 | h0
  · exact nonneg k h0 hk
  · by_cases hm : k = -1
    · subst hm
      have hε1 : ε = 1 := by
        obtain ⟨r, hr⟩ := hk
        omega
      subst hε1
      rw [show (-1 : ℤ) + 2 = 1 by norm_num, extend_of_nonneg (by norm_num),
        extend_of_neg (by norm_num)]
      simp only [Int.natAbs_one, Int.natAbs_neg, Nat.reduceDiv, Int.cast_neg, Int.cast_one]
      rcases hc with hc | hc
      · rw [hc]
        ring
      · rw [hc]
        push_cast
        ring
    · have hk' : Even (-k - 2 - ε) := by
        obtain ⟨r, hr⟩ := hk
        exact ⟨-r - 1 - ε, by omega⟩
      exact recurrence_of_reflect hs hσ hk (nonneg (-k - 2) (by omega) hk')

theorem extend_ne_zero_iff {σ : ℂ} {a : ℕ → ℂ} (hσ : σ ≠ 0) (k : ℤ) :
    extend σ a k ≠ 0 ↔ a (k.natAbs / 2) ≠ 0 := by
  unfold extend
  split_ifs <;> simp [hσ]

theorem neg_one_pow_sq (n : ℕ) : ((-1 : ℂ) ^ n) ^ 2 = 1 := by
  rw [← pow_mul, pow_mul', neg_one_sq, one_pow]

/-! ## The generic multiplier -/

/-- `∏_{i<m} (ε + 2i + 1 - ν) / (ε + 2i + 1 + ν)`, the value of the generic multiplier at
`ε + 2m`. -/
def genericSeq (ν : ℂ) (ε : ℤ) (m : ℕ) : ℂ :=
  ∏ i ∈ range m, ((ε : ℂ) + 2 * i + 1 - ν) / ((ε : ℂ) + 2 * i + 1 + ν)

/-- The generic multiplier: `genericSeq ν ε m` at `ε + 2m` and `(-1)^ε` times it at
`-(ε + 2m)`. -/
def genericMultiplier (ν : ℂ) (ε : ℤ) : ℤ → ℂ :=
  extend ((-1) ^ ε.natAbs) (genericSeq ν ε)

theorem genericSeq_denom_ne_zero {ν : ℂ} (hν : 0 < ν.re) {ε : ℤ} (hε : 0 ≤ ε) (i : ℕ) :
    (ε : ℂ) + 2 * i + 1 + ν ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  simp only [Complex.add_re, Complex.intCast_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, Complex.one_re, Complex.re_ofNat, Complex.im_ofNat, Complex.zero_re,
    mul_zero, sub_zero] at h'
  have hε' : (0 : ℝ) ≤ ε := by exact_mod_cast hε
  have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  linarith

theorem genericSeq_succ {ν : ℂ} (hν : 0 < ν.re) {ε : ℤ} (hε : 0 ≤ ε) (m : ℕ) :
    genericSeq ν ε (m + 1) * (ν + 1 + ε + 2 * m) =
      ((ε : ℂ) + 2 * m + 2 - (ν + 1)) * genericSeq ν ε m := by
  have hd := genericSeq_denom_ne_zero hν hε m
  rw [genericSeq, prod_range_succ, ← genericSeq]
  field_simp
  ring

theorem genericSeq_ne_zero {ν : ℂ} (hν : 0 < ν.re) {ε : ℤ} (hε : 0 ≤ ε)
    (hne : ∀ m : ℕ, ν ≠ (ε : ℂ) + 2 * m + 1) (m : ℕ) : genericSeq ν ε m ≠ 0 := by
  rw [genericSeq, prod_ne_zero_iff]
  intro i _
  exact div_ne_zero (sub_ne_zero.mpr (hne i).symm) (genericSeq_denom_ne_zero hν hε i)

theorem isRecurrent_genericMultiplier {ν : ℂ} (hν : 0 < ν.re) {ε : ℤ} (hε : ε = 0 ∨ ε = 1) :
    IsRecurrent (ν + 1) ε (genericMultiplier ν ε) :=
  isRecurrent_extend hε (neg_one_pow_sq _) (Or.inr rfl) fun m => by
    have h0 : 0 ≤ ε := by omega
    have := genericSeq_succ hν h0 m
    linear_combination this

theorem isSymmetric_genericMultiplier (ν : ℂ) {ε : ℤ} (hε : ε = 0 ∨ ε = 1) :
    IsSymmetric ε ((-1) ^ ε.natAbs) (genericMultiplier ν ε) :=
  isSymmetric_extend hε (neg_one_pow_sq _) (Or.inr rfl)

theorem genericMultiplier_ne_zero {ν : ℂ} (hν : 0 < ν.re) {ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    (hne : ∀ m : ℕ, ν ≠ (ε : ℂ) + 2 * m + 1) (k : ℤ) : genericMultiplier ν ε k ≠ 0 :=
  (extend_ne_zero_iff (pow_ne_zero _ (by norm_num)) k).mpr
    (genericSeq_ne_zero hν (by omega : 0 ≤ ε) hne _)

/-- **Generic multiplier.** For `0 < re ν` and `ν ≠ ε + 2m + 1` there is a symmetric solution
of the recurrence for `δ = ν + 1` without zeros on the parity class. -/
theorem exists_generic {ν : ℂ} (hν : 0 < ν.re) {ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    (hne : ∀ m : ℕ, ν ≠ (ε : ℂ) + 2 * m + 1) :
    ∃ μ : ℤ → ℂ, IsRecurrent (ν + 1) ε μ ∧ IsSymmetric ε ((-1) ^ ε.natAbs) μ ∧
      ∀ k : ℤ, Even (k - ε) → μ k ≠ 0 :=
  ⟨genericMultiplier ν ε, isRecurrent_genericMultiplier hν hε,
    isSymmetric_genericMultiplier ν hε, fun k _ => genericMultiplier_ne_zero hν hε hne k⟩

/-! ## The binomial and tail multipliers -/

/-- For `0 < ℓ`, `ε ∈ {0, 1}` and `ℓ - 1 ≡ ε (mod 2)`, write `ℓ = ε + 2h + 1`. -/
theorem exists_half {ℓ : ℕ} (hℓ : 0 < ℓ) {ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - 1 - ε)) :
    ∃ h : ℕ, ℓ = ε.toNat + 2 * h + 1 ∧ (ε.toNat : ℤ) = ε := by
  obtain ⟨r, hr⟩ := hpar
  exact ⟨r.toNat, by omega, by omega⟩

/-- `(-1)^m C(ℓ - 1, (ℓ - 1 + ε) / 2 + m)`, the value of the binomial multiplier at `ε + 2m`.
For `ℓ - 1 ≡ ε (mod 2)` the lower index is `(ε + 2m + ℓ - 1) / 2`. -/
def binomialSeq (ℓ : ℕ) (ε : ℤ) (m : ℕ) : ℂ :=
  (-1) ^ m * ((ℓ - 1).choose ((ℓ - 1 + ε.toNat) / 2 + m) : ℂ)

/-- The binomial multiplier: `binomialSeq ℓ ε m` at `ε + 2m` and `(-1)^ε` times it at
`-(ε + 2m)`. -/
def binomialMultiplier (ℓ : ℕ) (ε : ℤ) : ℤ → ℂ :=
  extend ((-1) ^ ε.natAbs) (binomialSeq ℓ ε)

/-- `C(m + (ℓ - 1 + ε) / 2, ℓ)`, the value of the tail multiplier at `ε + 2m`. For
`ℓ - 1 ≡ ε (mod 2)` the upper index is `(ε + 2m + ℓ - 1) / 2`. -/
def tailSeq (ℓ : ℕ) (ε : ℤ) (m : ℕ) : ℂ :=
  ((m + (ℓ - 1 + ε.toNat) / 2).choose ℓ : ℂ)

/-- The tail multiplier with sign `σ`: `tailSeq ℓ ε m` at `ε + 2m` and `σ` times it at
`-(ε + 2m)`. -/
def tailMultiplier (ℓ : ℕ) (ε : ℤ) (σ : ℂ) : ℤ → ℂ :=
  extend σ (tailSeq ℓ ε)

section Binomial

variable {ℓ : ℕ} {ε : ℤ} {h : ℕ}

theorem binomialSeq_eq (hl : ℓ = ε.toNat + 2 * h + 1) (m : ℕ) :
    binomialSeq ℓ ε m = (-1) ^ m * ((ε.toNat + 2 * h).choose (ε.toNat + h + m) : ℂ) := by
  rw [binomialSeq, show ℓ - 1 = ε.toNat + 2 * h by omega,
    show (ε.toNat + 2 * h + ε.toNat) / 2 + m = ε.toNat + h + m by omega]

theorem tailSeq_eq (hl : ℓ = ε.toNat + 2 * h + 1) (m : ℕ) :
    tailSeq ℓ ε m = ((m + ε.toNat + h).choose ℓ : ℂ) := by
  rw [tailSeq, show (ℓ - 1 + ε.toNat) / 2 = ε.toNat + h by omega, Nat.add_assoc]

theorem binomialSeq_succ (hl : ℓ = ε.toNat + 2 * h + 1) (he : (ε.toNat : ℤ) = ε) (m : ℕ) :
    binomialSeq ℓ ε (m + 1) * ((ℓ : ℂ) + 1 + ε + 2 * m) =
      ((ε : ℂ) + 2 * m + 2 - ((ℓ : ℂ) + 1)) * binomialSeq ℓ ε m := by
  rw [binomialSeq_eq hl, binomialSeq_eq hl]
  set e := ε.toNat
  have hεc : (ε : ℂ) = (e : ℂ) := by
    rw [← he]
    push_cast
    rfl
  have hlc : (ℓ : ℂ) = e + 2 * h + 1 := by
    rw [hl]
    push_cast
    ring
  have key : ((e + 2 * h).choose (e + h + (m + 1)) : ℂ) * ((e : ℂ) + h + m + 1) =
      ((e + 2 * h).choose (e + h + m) : ℂ) * ((h : ℂ) - m) := by
    have hN := Nat.choose_succ_right_eq (e + 2 * h) (e + h + m)
    rcases le_or_gt m h with hm | hm
    · rw [show e + 2 * h - (e + h + m) = h - m by omega] at hN
      have := congrArg (fun x : ℕ => (x : ℂ)) hN
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hm] at this
      rw [show e + h + (m + 1) = e + h + m + 1 by ring]
      linear_combination this
    · rw [Nat.choose_eq_zero_of_lt (by omega : e + 2 * h < e + h + (m + 1)),
        Nat.choose_eq_zero_of_lt (by omega : e + 2 * h < e + h + m)]
      simp
  rw [hεc, hlc]
  linear_combination (-2 * (-1 : ℂ) ^ m) * key

theorem binomialSeq_ne_zero_iff (hl : ℓ = ε.toNat + 2 * h + 1) (m : ℕ) :
    binomialSeq ℓ ε m ≠ 0 ↔ m ≤ h := by
  rw [binomialSeq_eq hl, mul_ne_zero_iff, Nat.cast_ne_zero]
  simp only [ne_eq, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, false_and, not_false_eq_true,
    true_and, Nat.choose_eq_zero_iff, not_lt]
  omega

theorem tailSeq_succ (hl : ℓ = ε.toNat + 2 * h + 1) (he : (ε.toNat : ℤ) = ε) (m : ℕ) :
    tailSeq ℓ ε (m + 1) * ((1 - (ℓ : ℂ)) + ε + 2 * m) =
      ((ε : ℂ) + 2 * m + 2 - (1 - (ℓ : ℂ))) * tailSeq ℓ ε m := by
  rw [tailSeq_eq hl, tailSeq_eq hl]
  set e := ε.toNat
  have hεc : (ε : ℂ) = (e : ℂ) := by
    rw [← he]
    push_cast
    rfl
  have hlc : (ℓ : ℂ) = e + 2 * h + 1 := by
    rw [hl]
    push_cast
    ring
  have key : ((m + e + h).choose ℓ : ℂ) * ((m : ℂ) + e + h + 1) =
      ((m + 1 + e + h).choose ℓ : ℂ) * ((m : ℂ) - h) := by
    have hN := Nat.choose_mul_succ_eq (m + e + h) ℓ
    rw [show m + e + h + 1 = m + 1 + e + h by ring] at hN
    rcases le_or_gt ℓ (m + 1 + e + h) with hm | hm
    · have := congrArg (fun x : ℕ => (x : ℂ)) hN
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hm] at this
      rw [hlc] at this
      linear_combination this
    · rw [Nat.choose_eq_zero_of_lt (by omega : m + 1 + e + h < ℓ),
        Nat.choose_eq_zero_of_lt (by omega : m + e + h < ℓ)]
      simp
  rw [hεc, hlc]
  linear_combination (-2 : ℂ) * key

theorem tailSeq_ne_zero_iff (hl : ℓ = ε.toNat + 2 * h + 1) (m : ℕ) :
    tailSeq ℓ ε m ≠ 0 ↔ h < m := by
  rw [tailSeq_eq hl, Ne, Nat.cast_eq_zero, Nat.choose_eq_zero_iff, not_lt]
  omega

end Binomial

theorem isRecurrent_binomialMultiplier {ℓ : ℕ} (hℓ : 0 < ℓ) {ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - 1 - ε)) :
    IsRecurrent ((ℓ : ℂ) + 1) ε (binomialMultiplier ℓ ε) := by
  obtain ⟨h, hl, he⟩ := exists_half hℓ hε hpar
  exact isRecurrent_extend hε (neg_one_pow_sq _) (Or.inr rfl) fun m => by
    linear_combination binomialSeq_succ hl he m

theorem isSymmetric_binomialMultiplier (ℓ : ℕ) {ε : ℤ} (hε : ε = 0 ∨ ε = 1) :
    IsSymmetric ε ((-1) ^ ε.natAbs) (binomialMultiplier ℓ ε) :=
  isSymmetric_extend hε (neg_one_pow_sq _) (Or.inr rfl)

theorem binomialMultiplier_ne_zero_iff {ℓ : ℕ} (hℓ : 0 < ℓ) {ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - 1 - ε)) {k : ℤ} (hk : Even (k - ε)) :
    binomialMultiplier ℓ ε k ≠ 0 ↔ |k| < ℓ := by
  obtain ⟨h, hl, he⟩ := exists_half hℓ hε hpar
  rw [binomialMultiplier, extend_ne_zero_iff (pow_ne_zero _ (by norm_num)),
    binomialSeq_ne_zero_iff hl, Int.abs_eq_natAbs]
  obtain ⟨r, hr⟩ := hk
  omega

theorem isRecurrent_tailMultiplier {ℓ : ℕ} (hℓ : 0 < ℓ) {ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - 1 - ε)) {σ : ℂ} (hσ : σ ^ 2 = 1) :
    IsRecurrent (1 - (ℓ : ℂ)) ε (tailMultiplier ℓ ε σ) := by
  obtain ⟨h, hl, he⟩ := exists_half hℓ hε hpar
  refine isRecurrent_extend hε hσ (Or.inl ?_) fun m => by
    linear_combination tailSeq_succ hl he m
  by_contra h0
  rw [← Ne, tailSeq_ne_zero_iff hl] at h0
  omega

theorem isSymmetric_tailMultiplier {ℓ : ℕ} (hℓ : 0 < ℓ) {ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - 1 - ε)) {σ : ℂ} (hσ : σ ^ 2 = 1) :
    IsSymmetric ε σ (tailMultiplier ℓ ε σ) := by
  obtain ⟨h, hl, he⟩ := exists_half hℓ hε hpar
  refine isSymmetric_extend hε hσ (Or.inl ?_)
  by_contra h0
  rw [← Ne, tailSeq_ne_zero_iff hl] at h0
  omega

theorem tailMultiplier_ne_zero_iff {ℓ : ℕ} (hℓ : 0 < ℓ) {ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - 1 - ε)) {σ : ℂ} (hσ : σ ^ 2 = 1) {k : ℤ} (hk : Even (k - ε)) :
    tailMultiplier ℓ ε σ k ≠ 0 ↔ (ℓ : ℤ) < |k| := by
  obtain ⟨h, hl, he⟩ := exists_half hℓ hε hpar
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    norm_num at hσ
  rw [tailMultiplier, extend_ne_zero_iff hσ0, tailSeq_ne_zero_iff hl, Int.abs_eq_natAbs]
  obtain ⟨r, hr⟩ := hk
  omega

/-- **Binomial multiplier.** For `0 < ℓ` with `ℓ - 1 ≡ ε (mod 2)` there is a symmetric solution
of the recurrence for `δ = ℓ + 1` whose support on the parity class is `|k| < ℓ`. -/
theorem exists_binomial {ℓ : ℕ} (hℓ : 0 < ℓ) {ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - 1 - ε)) :
    ∃ μ : ℤ → ℂ, IsRecurrent ((ℓ : ℂ) + 1) ε μ ∧ IsSymmetric ε ((-1) ^ ε.natAbs) μ ∧
      ∀ k : ℤ, Even (k - ε) → (μ k ≠ 0 ↔ |k| < ℓ) :=
  ⟨binomialMultiplier ℓ ε, isRecurrent_binomialMultiplier hℓ hε hpar,
    isSymmetric_binomialMultiplier ℓ hε, fun _ hk =>
      binomialMultiplier_ne_zero_iff hℓ hε hpar hk⟩

/-- **Tail multiplier.** For `0 < ℓ` with `ℓ - 1 ≡ ε (mod 2)` and any sign `σ` there is a
solution of the recurrence for `δ = 1 - ℓ`, symmetric for `σ`, whose support on the parity
class is `|k| > ℓ`. -/
theorem exists_tail {ℓ : ℕ} (hℓ : 0 < ℓ) {ε : ℤ} (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - 1 - ε)) {σ : ℂ} (hσ : σ ^ 2 = 1) :
    ∃ P : ℤ → ℂ, IsRecurrent (1 - (ℓ : ℂ)) ε P ∧ IsSymmetric ε σ P ∧
      ∀ k : ℤ, Even (k - ε) → (P k ≠ 0 ↔ (ℓ : ℤ) < |k|) :=
  ⟨tailMultiplier ℓ ε σ, isRecurrent_tailMultiplier hℓ hε hpar hσ,
    isSymmetric_tailMultiplier hℓ hε hpar hσ, fun _ hk =>
      tailMultiplier_ne_zero_iff hℓ hε hpar hσ hk⟩

end Langlands.Archimedean.RealBlockMultiplier
